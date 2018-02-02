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
import scala.collection.mutable.{ArrayBuffer => MSeq}

class EnumTransformer(mat: MetaAnnotationTransformer) {

  def transform(name: Vector[String], tree: Tree): Unit = {
    tree match {
      case tree: Defn.Object =>
        if (tree.templ.early.nonEmpty ||
          tree.templ.inits.nonEmpty ||
          tree.templ.self.decltpe.nonEmpty ||
          tree.templ.self.name.value != "") {
          mat.error(tree.pos, s"Invalid @enum form on an object; it has to be of the form '@enum object ${tree.name.value} { ... }'.")
          return
        }
        var decls = Vector[Stat](
          q"""sealed trait Type extends _root_.org.sireum.Immutable with _root_.scala.Ordered[Type]  {
                def ordinal: $sireumZ

                def name: $sireumString

                final def hash: $sireumZ = hashCode

                final def isEqual(other: Type): $sireumB = this == other

                final def compare(that: Type): $scalaInt = this.ordinal.compareTo(that.ordinal)

                final def string: $sireumString = toString
              }
           """,
          q"""final def byName(name: $sireumString): $sireumOption[Type] =
                elements.elements.find(_.name == name) match {
                  case _root_.scala.Some(v) => $sireumSomeQ(v)
                  case _ => $sireumNoneQ()
              }
           """,
          q"""final def byOrdinal(n: $sireumZ): $sireumOption[Type] =
                if (0 <= n && n < elements.size) $sireumSomeQ(elements(n)) else $sireumNoneQ()
           """
        )
        var elements = Vector[Term.Name]()
        var i = 0
        for (stat <- tree.templ.stats) {
          val sym = stat match {
            case Lit.Symbol(s) => s.name
            case Term.Apply(Term.Select(Term.Name("scala"), Term.Name("Symbol")), Seq(Lit.String(s))) => s
            case _ =>
              mat.error(stat.pos, s"Slang @enum can only have symbols for enum element names: ${stat.syntax}")
              return
          }
          val tname = Term.Name(sym)
          val ostats = List[Stat](
            q"def ordinal: $sireumZ = ${Lit.Int(i)}",
            q"def name: $sireumString = ${Lit.String(sym)}"
          )
          decls :+= q"final case object $tname extends Type { ..$ostats }"
          elements :+= tname
          i += 1
        }
        decls ++= Vector[Stat](
          q"val numOfElements: $sireumZ = ${Lit.Int(i)}",
          q"val elements: $sireumISZ[Type] = $sireumISZQ[Type](..${elements.toList})"
        )
        mat.objectMembers.getOrElseUpdate(name, MSeq()) ++= decls.map(_.syntax)
        mat.objectSupers.getOrElseUpdate(name, MSeq()) += enumSig.syntax
      case _ =>
        mat.error(tree.pos, "Slang @enum can only be used on an object.")
    }
  }
}
