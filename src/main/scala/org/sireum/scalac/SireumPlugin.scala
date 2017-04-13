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
  val dollar = Ident("$")

  final class Transformer(unit: CompilationUnit,
                          var declaredVars: List[String]) extends TypingTransformer(unit) {
    override def transform(tree: global.Tree): global.Tree = tree match {
      case tree: Block =>
        val dvs = declaredVars
        val r = super.transform(tree)
        declaredVars = dvs
        r
      case tree: ValDef =>
        declaredVars ::= tree.name.decoded
        if (tree.rhs == EmptyTree || tree.rhs == dollar) tree
        else tree.copy(rhs = Apply(Ident("_assign"), List(tree.rhs)))
      case tree: Assign =>
        tree.copy(rhs = Apply(Ident("_assign"), List(tree.rhs)))
      case tree@Apply(Select(_, TermName("update")), List(t2, t3)) =>
        tree.copy(args = List(t2, Apply(Ident("_assign"), List(t3))))
      case tree: Return =>
        val cleanups = for (v <- declaredVars) yield Apply(Ident("_cleanup"), List(Ident(v)))
        Block((tree :: cleanups).reverse: _*)
      case _ => super.transform(tree)
    }
  }

  def newPhase(prev: Phase): StdPhase = new StdPhase(prev) {
    def apply(unit: CompilationUnit): Unit = {
      var isSireum = unit.source.file.hasExtension("logika") || (unit.source.file.hasExtension("sc") &&
        (unit.body.children.headOption match {
          case Some(x: Import) if x.selectors == List(ImportSelector.wild) =>
            x.expr match {
              case Select(Ident(org), sireum) => org.decoded == "org" && sireum.decoded == "sireum"
              case Select(Select(Ident(org), sireum), logika) =>
                org.decoded == "org" && sireum.decoded == "sireum" && logika.decoded == "logika"
              case _ => false
            }
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
        isSireum = "//#Sireum" == firstLine || "//#Logika" == firstLine
      }
      if (isSireum) unit.body = new Transformer(unit, List()).transform(unit.body)
    }
  }
}