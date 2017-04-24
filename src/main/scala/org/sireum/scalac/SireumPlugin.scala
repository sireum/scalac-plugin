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

  def isDollar(t: Any): Boolean = t match {
    case q"$$" => true
    case _ => false
  }

  def isUninit(t: Any): Boolean = t match {
    case q"??" => true
    case _ => false
  }


  val unitCons = Literal(Constant(()))

  final class Transformer(unit: CompilationUnit,
                          inTrait: Boolean) extends global.Transformer {
    def sup(tree: global.Tree): global.Tree = super.transform(tree)

    def trans(tree: Any): global.Tree = transform(tree.asInstanceOf[global.Tree])

    override def transform(tree: global.Tree): global.Tree = tree match {
      case Apply(Select(Apply(Ident(TermName("StringContext")), _), TermName("s")), _) => tree
      case Apply(Select(Ident(TermName("tup")), TermName("update")), _) => tree
      case q"$_ trait $_[..$_] extends { ..$_ } with ..$_ { $_ => ..$_ }" =>
        new Transformer(unit, inTrait = true).sup(tree)
      case tree: DefDef if inTrait =>
        tree.rhs match {
          case Apply(Select(Apply(Ident(TermName("StringContext")), List(Literal(Constant(_: String)))), TermName("c")), List()) =>
            tree.copy(rhs = EmptyTree)
          case _ => tree
        }
      case Literal(Constant(n: Int)) => q"StringContext(${BigInt(n).toString}).z()"
      case Literal(Constant(n: Long)) => q"StringContext(${BigInt(n).toString}).z()"
      case tree: CaseDef =>
        val g = transform(tree.guard)
        val b = transform(tree.body)
        if ((g ne tree.guard) || (b ne tree.body)) {
          tree.copy(guard = transform(tree.guard), body = transform(tree.body))
        } else tree
      case tree: Apply if tree.args.nonEmpty =>
        var changed = false
        val r = tree.copy(args = for (arg <- tree.args) yield arg match {
          case arg: Literal => transform(arg)
          case arg: AssignOrNamedArg =>
            changed = true
            arg.copy(rhs = q"_assign(${transform(arg.rhs)})")
          case _ =>
            changed = true
            q"_assign(${transform(arg)})"
        })
        if (changed) r else tree
      case tree: Assign => tree.copy(rhs = q"_assign(${transform(tree.rhs)})")
      case q"$expr1(..$exprs2) = $expr" =>
        q"${trans(expr1)}(..${exprs2.map(trans)}) = _assign(${trans(expr)})"
      case q"(..$exprs)" if exprs.size > 1 => q"(..${exprs.map(e => q"_assign(${trans(e)})")})"
      case q"$mods val ${tname: TermName}: $tpt = $expr" =>
        if (!(expr == EmptyTree || isDollar(expr)))
          q"$mods var $tname: $tpt = _assign(${trans(expr)})"
        else tree
      case q"$mods var ${tname: TermName}: $tpt = $expr" =>
        if (isUninit(expr)) {
          tpt match {
            case Ident(TypeName(n)) => n match {
              case "B" => q"$mods var $tname: $tpt = F"
              case "Z" => q"""$mods var $tname: $tpt = z"0""""
              case "Z8" => q"""$mods var $tname: $tpt = z8"0""""
              case "Z16" => q"""$mods var $tname: $tpt = z16"0""""
              case "Z32" => q"""$mods var $tname: $tpt = z32"0""""
              case "Z64" => q"""$mods var $tname: $tpt = z64"0""""
              case "N" => q"""$mods var $tname: $tpt = n"0""""
              case "N8" => q"""$mods var $tname: $tpt = n8"0""""
              case "N16" => q"""$mods var $tname: $tpt = n16"0""""
              case "N32" => q"""$mods var $tname: $tpt = n32"0""""
              case "N64" => q"""$mods var $tname: $tpt = n64"0""""
              case "S8" => q"""$mods var $tname: $tpt = s8"0""""
              case "S16" => q"""$mods var $tname: $tpt = s16"0""""
              case "S32" => q"""$mods var $tname: $tpt = s32"0""""
              case "S64" => q"""$mods var $tname: $tpt = s64"0""""
              case "U8" => q"""$mods var $tname: $tpt = u8"0""""
              case "U16" => q"""$mods var $tname: $tpt = u16"0""""
              case "U32" => q"""$mods var $tname: $tpt = u32"0""""
              case "U64" => q"""$mods var $tname: $tpt = u64"0""""
              case "F32" => q"""$mods var $tname: $tpt = f32"0.0""""
              case "F64" => q"""$mods var $tname: $tpt = f64"0.0""""
              case "R" => q"""$mods var $tname: $tpt = r"0.0""""
              case _ => q"$mods var $tname: $tpt = null"
            }
            case _ => q"$mods var $tname: $tpt = null"
          }
        } else if (!(expr == EmptyTree || isDollar(expr)))
          q"$mods var $tname: $tpt = _assign(${trans(expr)})"
        else tree
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
        isSireum = firstLine.contains("#Sireum")
      }
      if (isSireum) unit.body = new Transformer(unit, inTrait = false).transform(unit.body)
    }
  }
}