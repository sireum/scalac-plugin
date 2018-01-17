/*
 Copyright (c) 2017, Robby, Kansas State University
 All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions are met:

 1. Redistributions of source code must retain the above copyright notice, this
    list of conditions and the following disclaimer.
 2. Redistributions in binary form must reproduce the above copyright notice,
    this list of conditions and the following disclaimer in the documentation
    and/or other materials provided with the distribution.

 THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
 ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package org.sireum.scalac

import scala.meta._
import MetaAnnotationTransformer._

class MemoizeTransformer(mat: MetaAnnotationTransformer) {
  def transform(name: Vector[String], tree: Tree): Unit = {
    tree match {
      case tree: Defn.Def =>
        if (tree.paramss.size != 1 || tree.paramss.head.isEmpty) {
          mat.error(tree.pos, "Slang @memoize methods should only have one list of non-empty parameters.")
          return
        }
        if (tree.decltpe.isEmpty) {
          mat.error(tree.pos, "Slang @memoize methods should be explicitly typed.")
          return
        }
        val rwMap = tree.parent.flatMap(_.parent) match {
          case Some(q"package $_ { ..$_ }") => mat.objectMemberReplace
          case Some(_: Defn.Object) => mat.objectMemberReplace
          case Some(_: Defn.Class) | Some(_: Defn.Trait) => mat.classMemberReplace
          case x =>
            mat.error(tree.pos, s"Slang @memoize methods should only be inside an object, a class, or a trait: ${x}.")
            return
        }
        val returnType = tree.decltpe.get
        var allParamTypes = Vector[Type]()
        var paramTypes = Vector[Type]()
        var params = Vector[Term.Name]()
        var hiddenParamTypes = Vector[Type]()
        var hiddenParams = Vector[Term.Name]()
        for (p <- tree.paramss.head) {
          val pname = Term.Name(p.name.value)
          p.decltpe match {
            case Some(tpe) =>
              allParamTypes :+= tpe
              if (p.mods.exists {
                case mod"@hidden" => true
                case _ => false
              }) {
                hiddenParamTypes :+= tpe
                hiddenParams :+= pname
              } else {
                paramTypes :+= tpe
                params :+= pname
              }
            case _ =>
              mat.error(tree.pos, "Unsupported Slang @memoize method parameter form.")
              return
          }
        }
        val (argType, arg) =
          if (paramTypes.length == 1) (paramTypes.head, params.head)
          else (t"(..${paramTypes.toList})", q"(..${params.toList})")
        var inits = List[Stat]()
        var assertions = List[Stat]()
        var hiddenVars = List[Stat]()
        for ((p, pt) <- hiddenParams.zip(hiddenParamTypes).toList) {
          val pvar = Term.Name("_" + p.value)
          hiddenVars :+= q"var ${Pat.Var(pvar)}: ${Some(pt)} = null"
          inits :+= q"""if ($pvar == null) $pvar = $p"""
          assertions :+= q"""assert($pvar eq $p, "@hidden parameter " + ${Lit.String(p.value)} + " differs from the first invocation argument.")"""
        }
        val body =
          q"""{
                def _internal: $returnType = { $$body$$ }

                {
                  ..${inits.reverse}
                  ..${assertions.reverse}
                }

                val arg = $arg
                cache.get(arg) match {
                  case scala.Some(r) => return r
                  case _ =>
                }
                val r = _internal
                cache(arg) = r
                r
              }
           """
        val cacheVar = {
          val cacheInit =
            q"""{
                  import scala.collection.JavaConverters._
                  (new java.util.concurrent.ConcurrentHashMap[$argType, $returnType]()).asScala
                }"""
          q"val cache: scala.collection.mutable.Map[$argType, $returnType] = $cacheInit"
        }
        val newName = Term.Name("_" + tree.name.value)
        val newStat = tree.copy(name = newName, body = body)
        val fnType =
          if (allParamTypes.size == 1) t"${allParamTypes.head} => $returnType"
          else t"(..${allParamTypes.toList}) => $returnType"
        rwMap(name :+ tree.name.value) = Defn.Val(List(Mod.Lazy()), List[Pat](Pat.Var(Term.Name(tree.name.value))), Some(fnType),
          q"{ ..${hiddenVars ++ List(cacheVar, newStat, q"$newName _")} }").syntax
      case _ => mat.error(tree.pos, "Slang @memoize can only be used on method definitions.")
    }
  }
}
