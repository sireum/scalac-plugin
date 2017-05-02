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

  implicit class CopyPos(val t: Any) {
    def copyPos(tree: Any): global.Tree = {
      val t2 = t.asInstanceOf[global.Tree]
      t2.pos = tree.asInstanceOf[global.Tree].pos
      t2
    }
  }

  import global._

  override val phaseName = "sireum"
  override val runsRightAfter = Some("parser")
  override val runsAfter: List[String] = runsRightAfter.toList
  override val runsBefore: List[String] = List[String]("namer")

  def isDollar(t: Any): Boolean = t match {
    case q"$$" => true
    case _ => false
  }

  val unitCons = Literal(Constant(()))

  final class Transformer(unit: CompilationUnit,
                          var inTrait: Boolean) extends TypingTransformer(unit) {
    def sup(tree: global.Tree): global.Tree = super.transform(tree)

    def trans(tree: Any): global.Tree = transform(tree.asInstanceOf[global.Tree])

    def pos(tree: Any): global.Position = tree.asInstanceOf[global.Tree].pos

    override def transform(tree: global.Tree): global.Tree = tree match {
      case Apply(Select(Apply(Ident(TermName("StringContext")), _), TermName("s")), _) => tree
      case tree@Apply(Select(Ident(TermName(f)), TermName("update")), l) if f == "up" || f == "pat" =>
        tree.copy(args = l.dropRight(1) ++ l.takeRight(1).map(transform)).copyPos(tree)
      case q"$_ trait $_[..$_] extends { ..$_ } with ..$_ { $_ => ..$_ }" =>
        val oldInTrait = inTrait
        inTrait = true
        val tree2 = sup(tree)
        inTrait = oldInTrait
        tree2.copyPos(tree)
      case tree: DefDef =>
        tree.rhs match {
          case rhs@Apply(sc@Select(Apply(Ident(TermName("StringContext")), _), TermName("l")), _) =>
            if (inTrait) tree.copy(rhs = EmptyTree).copyPos(tree)
            else tree.copy(rhs = rhs.copy(fun = sc.copy(name = TermName("lDef")).copyPos(sc)).copyPos(rhs)).copyPos(tree)
          case _ => sup(tree)
        }
      case tree@Apply(sc@Select(Apply(Ident(TermName("StringContext")), _), TermName("l")), _) =>
        tree.copy(fun = sc.copy(name = TermName("lUnit")).copyPos(sc)).copyPos(tree)
      case Literal(Constant(n: Int)) => q"StringContext(${n.toString}).z()".copyPos(tree)
      case Literal(Constant(n: Long)) => q"StringContext(${n.toString}).z()".copyPos(tree)
      case tree: CaseDef =>
        val g = transform(tree.guard)
        val b = transform(tree.body)
        if ((g ne tree.guard) || (b ne tree.body))
          tree.copy(guard = transform(tree.guard), body = transform(tree.body)).copyPos(tree)
        else tree
      case tree: Apply if tree.args.nonEmpty =>
        var changed = false
        val r = tree.copy(args = for (arg <- tree.args) yield arg match {
          case arg: Literal => val r = transform(arg); changed ||= r ne arg; r
          case arg: AssignOrNamedArg =>
            changed = true
            arg.copy(rhs = q"_assign(${transform(arg.rhs)})".copyPos(arg.rhs)).copyPos(arg)
          case _ => changed = true; q"_assign(${transform(arg)})".copyPos(arg)
        })
        if (changed) r.copyPos(tree) else tree
      case tree: Assign =>
        tree.copy(rhs = q"_assign(${transform(tree.rhs)})".copyPos(tree.rhs)).copyPos(tree)
      case q"$expr1(..$exprs2) = $expr" =>
        q"${trans(expr1)}(..${exprs2.map(trans)}) = ${q"_assign(${trans(expr)})".copyPos(expr)}".copyPos(tree)
      case q"(..$exprs)" if exprs.size > 1 =>
        q"(..${exprs.map(e => q"_assign(${trans(e)})".copyPos(e))})".copyPos(tree)
      case q"$mods val $pat: $tpt = $expr" =>
        if (!(expr == EmptyTree || isDollar(expr)))
          q"$mods var $pat: $tpt = ${q"_assign(${trans(expr)})".copyPos(expr)}"
        else tree
      case q"$mods var $pat: $tpt = $expr" =>
        if (!(expr == EmptyTree || isDollar(expr)))
          q"$mods var $pat: $tpt = ${q"_assign(${trans(expr)})".copyPos(expr)}"
        else tree
      case _ =>
        val tree2 = super.transform(tree)
//        if (tree2 ne tree) {
//          println(s"${tree2.pos.source.file.canonicalPath} [${tree2.pos.line}, ${tree2.pos.column}]: ${showCode(tree2)}")
//        }
        tree2
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
        isSireum = firstLine.contains("#Sireum")
      }
      if (isSireum) unit.body = new Transformer(unit, inTrait = false).transform(unit.body)
    }
  }
}