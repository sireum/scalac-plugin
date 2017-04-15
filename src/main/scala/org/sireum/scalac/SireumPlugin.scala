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

import scala.tools.nsc.Global
import scala.tools.nsc.Phase
import scala.tools.nsc.plugins.Plugin
import scala.tools.nsc.plugins.PluginComponent
import scala.tools.nsc.transform.TypingTransformers

class SireumPlugin(override val global: Global) extends Plugin {
  override val name = "sireum"
  override val description = "Compiler plugin for the Sireum Scala subset."
  override val components: List[PluginComponent] = List(new SireumComponent(global))
}

final class SireumComponent(val global: Global) extends PluginComponent with TypingTransformers {

  import global._

  override val phaseName = "sireum"
  override val runsRightAfter = Some("parser")
  override val runsAfter: List[String] = runsRightAfter.toList
  override val runsBefore: List[String] = List[String]("namer")
  def isDollar(t: Tree): Boolean = t match {
    case q"$$" => true
    case _ => false
  }
  val unitCons = Literal(Constant(()))

  final class Transformer(unit: CompilationUnit,
                          var methodName: Option[TermName],
                          var declaredVars: List[String]) extends TypingTransformer(unit) {
    override def transform(tree: global.Tree): global.Tree = tree match {
      case tree: DefDef =>
        val mn = methodName
        val dvs = declaredVars
        methodName = Some(tree.name)
        declaredVars = List()
        val r = super.transform(tree)
        declaredVars = dvs
        methodName = mn
        r
      case q"{ ..$stats }" =>
        val dvs = declaredVars
        val r = super.transform(tree)
        val diffVars = declaredVars.take(declaredVars.size - dvs.size)
        val r3 = if (diffVars.nonEmpty) {
          //println(s"Here $diffVars")
          val cs: List[Tree] =
            (for (v <- declaredVars.take(declaredVars.size - dvs.size))
              yield q"_cleanup(${Ident(v)})").reverse
          declaredVars = dvs
          val r2 = r match {
            case r: Block =>
              r.expr match {
                case _: Assign | _: ValDef => Block(r.stats ++ (r.expr :: cs), unitCons)
                case _ => Block(r.stats ++ cs, r.expr)
              }
          }
          // println(showCode(r2))
          r2
        } else r
        //println(showCode(r3))
        r3
      case q"$mods val ${tname: TermName}: $tpt = $expr" =>
        if (methodName.nonEmpty)
          declaredVars = tname.decoded :: declaredVars
        if (!(expr == EmptyTree || isDollar(expr.asInstanceOf[Tree])))
          return q"$mods var $tname: $tpt = _assign($expr)"
        tree
      case q"$mods var ${tname: TermName}: $tpt = $expr" =>
        if (methodName.nonEmpty)
          declaredVars = tname.decoded :: declaredVars
        if (!(expr == EmptyTree || isDollar(expr.asInstanceOf[Tree])))
          return q"$mods var $tname: $tpt = _assign($expr)"
        tree
      case q"$lhs = $rhs" => q"$lhs = _assign($rhs)"
      case q"$expr1(..$exprs2) = $expr" => q"$expr1(..$exprs2) = _assign($expr)"
      case _ => super.transform(tree)
    }
  }

  def newPhase(prev: Phase): StdPhase = new StdPhase(prev) {
    def apply(unit: CompilationUnit): Unit = {
      var isSireum = unit.source.file.hasExtension("logika") || (unit.source.file.hasExtension("sc") &&
        (unit.body.children.headOption match {
          case Some(x) if x == q"import org.sireum._" || x == q"import org.sireum.logika._" => true
          case _ => false
        }))
      if (!isSireum) {
        val cs = unit.source.content
        val i = cs.indexOf('\n')
        val sb = new StringBuilder
        if (i >= 0) {
          for (j <- 0 until i) cs(j) match {
            case '\t' | '\r' | ' ' =>
            case c => sb.append(c)
          }
        }
        val firstLine = sb.toString
        isSireum = "//#Sireum" == firstLine
      }
      if (isSireum) unit.body = new Transformer(unit, None, List()).transform(unit.body)
    }
  }
}