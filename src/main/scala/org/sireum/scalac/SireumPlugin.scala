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

import java.util

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

object SireumComponent {
  val ops = Set("+", "-", "*", "/", "%", "==", "!=", "<", ">", ">=", "<=", "&", "|", "|^", "+:", ":+", "++", "--")
}

import SireumComponent._

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
                          var inExp: Boolean,
                          var inPat: Boolean,
                          var inTrait: Boolean) extends TypingTransformer(unit) {
    val seen: util.IdentityHashMap[global.Tree, Boolean] = new util.IdentityHashMap(16 * 1024)

    def sup(tree: global.Tree): global.Tree = super.transform(tree)

    def trans(tree: Any): global.Tree = transform(tree.asInstanceOf[global.Tree])

    def assignNoTrans(tree: global.Tree) =
      if (inPat) tree else q"_assign($tree)".copyPos(tree)

    def assign(tree: Any): global.Tree = tree match {
      case _: Literal => trans(tree)
      case _: Function => trans(tree)
      case Apply(Select(Apply(Ident(TermName("StringContext")), _), _), _) => trans(tree)
      case _ => assignNoTrans(trans(tree))
    }

    def pos(tree: Any): global.Position = tree.asInstanceOf[global.Tree].pos

    def transformApply(tree: Apply): global.Tree = {
      def hasInnerApply(tree: global.Tree): Boolean = tree match {
        case _: Apply => true
        case q"(..$exprs)" if exprs.size > 1 =>
          for (e <- exprs) {
            if (hasInnerApply(e.asInstanceOf[global.Tree])) return true
          }
          false
        case q"$_.super[$_].$_" => false
        case q"new { ..$_ } with ..$_ { $_ => ..$_ }" => false
        case tree: Typed => hasInnerApply(tree.expr)
        case tree: TypeApply => hasInnerApply(tree.fun)
        case tree: Select => hasInnerApply(tree.qualifier)
        case _: This | _: Literal | _: Ident | _: Function | EmptyTree => false
      }

      val oldInExp = inExp
      inExp = true
      var changed = false
      val shouldNotAssign = (tree match {
        case Apply(Select(_, op), _) if ops.contains(op.decoded) => true
        case _ => oldInExp
      }) || hasInnerApply(tree.fun)
      val r = tree.copy(fun = {
        val r = transform(tree.fun);
        changed ||= r ne tree.fun;
        r
      },
        args = for (arg <- tree.args) yield arg match {
          case arg: Literal => val r = transform(arg); changed ||= r ne arg; r
          case arg: Function => val r = transform(arg); changed ||= r ne arg; r
          case arg@Apply(Select(Apply(Ident(TermName("StringContext")), _), _), _) =>
            val r = transform(arg); changed ||= r ne arg; r
          case arg: AssignOrNamedArg =>
            changed = true
            if (shouldNotAssign) arg.copy(rhs = transform(arg.rhs)).copyPos(arg)
            else arg.copy(rhs = assign(arg.rhs)).copyPos(arg)
          case _ => changed = true; if (shouldNotAssign) transform(arg) else assign(arg)
        })
      inExp = oldInExp
      if (changed) r.copyPos(tree) else tree
    }

    def fixPos(tree: global.Tree): global.Tree = {
      def rec(pos: Position, t: global.Tree): Unit = {
        if (seen.containsKey(t)) return
        seen.put(tree, true)
        if (t.pos == NoPosition) {
          t.pos = pos.makeTransparent
        }
        for (t2 <- t.children) {
          rec(t.pos, t2)
        }
      }

      rec(tree.pos, tree)
      tree
    }

    override def transform(tree: global.Tree): global.Tree = {
      val r = tree match {
        case tree: DefDef =>
          tree.rhs match {
            case rhs@Apply(sc@Select(Apply(Ident(TermName("StringContext")), _), TermName("l")), _) =>
              if (inTrait) tree.copy(rhs = EmptyTree).copyPos(tree)
              else tree.copy(rhs = rhs.copy(fun = sc.copy(name = TermName("lDef")).copyPos(sc)).copyPos(rhs)).copyPos(tree)
            case _ =>
              sup(tree)
          }
        case tree@Apply(sc@Select(Apply(Ident(TermName("StringContext")), _), TermName("l")), _) if !inPat =>
          tree.copy(fun = sc.copy(name = TermName("lUnit")).copyPos(sc)).copyPos(tree)
        case tree@Apply(Select(Ident(TermName("scala")), TermName("Symbol")), _) => tree
        case tree@Apply(Ident(TermName("StringContext")), _) => tree
        case q"$_ trait $_[..$_] extends { ..$_ } with ..$_ { $_ => ..$_ }" =>
          val oldInTrait = inTrait
          inTrait = true
          val tree2 = sup(tree)
          inTrait = oldInTrait
          tree2.copyPos(tree)
        case tree@Select(o, TermName("hash")) if !inPat =>
          Apply(Ident(TermName("_Z")).copyPos(tree), List(Select(transform(o), TermName("hashCode")).copyPos(tree))).copyPos(tree)
        case Literal(Constant(true)) => q"T".copyPos(tree)
        case Literal(Constant(false)) => q"F".copyPos(tree)
        case Literal(Constant(_: Char)) =>
          (if (inPat) pq"_XChar($tree)" else q"_2C($tree)").copyPos(tree)
        case Literal(Constant(o: Int)) =>
          (if (inPat) pq"_XInt($tree)" else q"StringContext(${o.toString}).z()").copyPos(tree)
        case Literal(Constant(o: Long)) =>
          (if (inPat) pq"_XLong($tree)" else q"StringContext(${o.toString}).z()").copyPos(tree)
        case Literal(Constant(o: Float)) =>
          (if (inPat) pq"_XFloat($tree)" else q"StringContext(${o.toString}).f32()").copyPos(tree)
        case Literal(Constant(o: Double)) =>
          (if (inPat) pq"_XDouble($tree)" else q"StringContext(${o.toString}).f64()").copyPos(tree)
        case Literal(Constant(_: String)) =>
          (if (inPat) pq"_XString($tree)" else q"_2String($tree)").copyPos(tree)
        case q"$mods val $pat: $tpt = $rhs" =>
          if (!(rhs == EmptyTree || isDollar(rhs))) rhs match {
            case rhs: Apply => q"$mods val $pat: $tpt = ${assignNoTrans(transformApply(rhs))}".copyPos(tree)
            case _ => q"$mods val $pat: $tpt = ${assign(rhs)}".copyPos(tree)
          } else tree
        case q"$mods var $pat: $tpt = $rhs" =>
          if (!(rhs == EmptyTree || isDollar(rhs))) rhs match {
            case rhs: Apply => q"$mods var $pat: $tpt = ${assignNoTrans(transformApply(rhs))}".copyPos(tree)
            case _ => q"$mods var $pat: $tpt = ${assign(rhs)}".copyPos(tree)
          } else tree
        case tree: Assign =>
          tree.rhs match {
            case rhs: Apply => tree.copy(rhs = assignNoTrans(transformApply(rhs))).copyPos(tree)
            case rhs => tree.copy(rhs = assign(rhs)).copyPos(tree)
          }
        case tree@Apply(Select(Ident(TermName(f)), TermName("update")), l) if !inPat && (f == "up" || f == "pat") =>
          tree.copy(args = l.dropRight(1) ++ l.takeRight(1).map(transform)).copyPos(tree)
        case q"$expr1(..$exprs2) = $expr" =>
          expr match {
            case rhs: Apply => q"${trans(expr1)}(..${exprs2.map(trans)}) = ${assignNoTrans(transformApply(rhs))}".copyPos(tree)
            case _ => q"${trans(expr1)}(..${exprs2.map(trans)}) = ${assign(expr)}".copyPos(tree)
          }
        case tree: If =>
          val oldInExp = inExp
          inExp = true
          val cond = transform(tree.cond)
          inExp = oldInExp
          val thenp = transform(tree.thenp)
          val elsep = transform(tree.elsep)
          if ((cond ne tree.cond) || (thenp ne tree.thenp) || (elsep ne tree.elsep)) If(cond, thenp, elsep).copyPos(tree) else tree
        case tree@q"while ($cond) $body" =>
          val oldInExp = inExp
          inExp = true
          val newCond = trans(cond)
          inExp = oldInExp
          val newBody = trans(body)
          if ((cond ne newCond) || (body ne newBody)) q"while ($newCond) $newBody".copyPos(tree) else tree
        case tree@q"do $body while ($cond)" =>
          val oldInExp = inExp
          inExp = true
          val newCond = trans(cond)
          inExp = oldInExp
          val newBody = trans(body)
          if ((cond ne newCond) || (body ne newBody)) q"do $newBody while ($newCond)".copyPos(tree) else tree
        case tree@q"for (..$enums) $body" =>
          val oldInExp = inExp
          inExp = true
          var hasChanged = false
          val newEnums = for (enum <- enums) yield {
            val newEnum = trans(enum)
            if (enum ne newEnum) hasChanged = true
            newEnum
          }
          inExp = oldInExp
          val newBody = trans(body)
          if (hasChanged || (body ne newBody)) q"for (..$newEnums) $newBody".copyPos(tree) else tree
        case tree@q"for (..$enums) yield $expr" =>
          val oldInExp = inExp
          inExp = true
          var hasChanged = false
          val newEnums = for (enum <- enums) yield {
            val newEnum = trans(enum)
            if (enum ne newEnum) hasChanged = true
            newEnum
          }
          inExp = oldInExp
          val newExpr = trans(expr)
          if (hasChanged || (expr ne newExpr)) q"for (..$newEnums) yield $newExpr".copyPos(tree) else tree
        case q"$expr match { case ..$cases }" =>
          val oldInExp = inExp
          inExp = true
          val newExpr = trans(expr)
          inExp = oldInExp
          var hasChanged = false
          val newCases = for (c <- cases) yield {
            val nc = trans(c)
            if (c ne nc) hasChanged = true
            nc
          }
          if (hasChanged || (expr ne newExpr)) q"$newExpr match { case ..$newCases }".copyPos(tree) else tree
        case tree: CaseDef =>
          val oldInPat = inPat
          inPat = true
          val pat = transform(tree.pat)
          inPat = oldInPat
          val oldInExp = inExp
          inExp = true
          val g = transform(tree.guard)
          inExp = oldInExp
          val b = transform(tree.body)
          if ((pat ne tree.pat) || (g ne tree.guard) || (b ne tree.body)) tree.copy(pat = pat, guard = g, body = b).copyPos(tree) else tree
        case q"(..$exprs)" if exprs.size > 1 => q"(..${exprs.map(assign)})".copyPos(tree)
        //case b: Block =>
        //  val b2 = sup(b)
        //  println(showCode(b2))
        //  b2
        case tree: Apply if !inPat => transformApply(tree)
        case _ =>
          val tree2 = super.transform(tree)
          //        if (tree2 ne tree) {
          //          println(s"${tree2.pos.source.file.canonicalPath} [${tree2.pos.line}, ${tree2.pos.column}]: ${showCode(tree2)}")
          //        }
          tree2
      }
      if (r ne tree) {
        fixPos(r)
      }
      r
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
      if (isSireum) {
        val t = new Transformer(unit, inExp = false, inPat = false, inTrait = false)
        unit.body = t.transform(unit.body)
        //println(s"Fix pos seen size ${t.seen.size}: ${unit.source.file.canonicalPath} ")
        t.seen.clear()
      }
    }
  }
}