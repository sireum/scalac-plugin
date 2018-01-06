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

  val importSireum = q"import org.sireum._"
  val importLogika = q"import org.sireum.logika._"

  override val phaseName = "sireum"
  override val runsRightAfter = Some("parser")
  override val runsAfter: List[String] = runsRightAfter.toList
  override val runsBefore: List[String] = List[String]("namer")

  val unitCons = Literal(Constant(()))

  implicit class CopyPos(val t: Any) {
    def copyPos(tree: Any): Tree = {
      val t2 = t.asInstanceOf[Tree]
      t2.pos = tree.asInstanceOf[Tree].pos
      t2
    }
    def copyPosT[T <: Tree](tree: T): T = {
      val t2 = t.asInstanceOf[T]
      t2.pos = tree.pos
      t2
    }
  }

  def sireumQ = q"_root_.org.sireum"
  def sireumT = q"$sireumQ.T"
  def sireumF = q"$sireumQ.F"
  def sireumZ = q"$sireumQ.Z"
  def sireumC = q"$sireumQ.C"
  def sireumF32 = q"$sireumQ.F32"
  def sireumF64 = q"$sireumQ.F64"
  def sireumString = q"$sireumQ.String"
  def assignQ = q"$sireumQ.helper.$$assign"

  def sireumCPat = pq"$sireumQ.C"
  def sireumZIntPat = q"$sireumQ.Z.Int"
  def sireumZLongPat = q"$sireumQ.Z.Long"
  def sireumF32Pat = pq"$sireumQ.F32"
  def sireumF64Pat = pq"$sireumQ.F64"
  def sireumStringPat = pq"$sireumQ.String"

  def fixPos(tree: Tree): Tree = {
    def rec(pos: Position, t: Tree): Unit = {
      if (t.pos == NoPosition) {
        t.pos = if (pos.isTransparent) pos else pos.makeTransparent
      }
      for (t2 <- t.children) {
        rec(t.pos, t2)
      }
    }

    rec(tree.pos, tree)
    tree
  }

  def isDollar(t: Any): Boolean = t match {
    case q"$$" => true
    case _ => false
  }

  final class SemanticsTransformer(unit: CompilationUnit,
                                   var inPat: Boolean,
                                   var inTrait: Boolean) extends TypingTransformer(unit) {
    def sup(tree: Tree): Tree = super.transform(tree)

    def trans(tree: Any): Tree = transform(tree.asInstanceOf[Tree])

    def assignNoTrans(tree: Tree): Tree =
      if (inPat) tree else q"$assignQ($tree)".copyPos(tree)

    def assign(tree: Any): Tree = tree match {
      case _: Literal => trans(tree)
      case _: Function => trans(tree)
      case Apply(Select(Apply(Ident(TermName("StringContext")), _), _), _) => trans(tree)
      case _ => assignNoTrans(trans(tree))
    }

    def pos(tree: Any): Position = tree.asInstanceOf[Tree].pos

    override def transform(tree: Tree): Tree = {
      val r = tree match {
        case tree: DefDef =>
          tree.rhs match {
            case rhs@Apply(sc@Select(Apply(Ident(TermName("StringContext")), _), TermName("l")), _) =>
              if (inTrait) tree.copy(rhs = q"$$").copyPos(tree)
              else tree.copy(rhs = rhs.copy(fun = sc.copy(name = TermName("lDef")).copyPos(sc)).copyPos(rhs)).copyPos(tree)
            case _ =>
              sup(tree)
          }
        case tree@Apply(sc@Select(Apply(Ident(TermName("StringContext")), _), TermName("l")), _) if !inPat =>
          tree.copy(fun = sc.copy(name = TermName("lUnit")).copyPos(sc)).copyPos(tree)
        case tree@Apply(Select(Ident(TermName("scala")), TermName("Symbol")), _) => tree
        case tree@Apply(Ident(TermName("StringContext")), _) => tree
        case q"$_ trait $_[..$_] extends { ..$_ } with ..$_ { $_ => ..$_ }" =>
          val classTree = tree.asInstanceOf[ClassDef]
          //if (classTree.mods.hasAnnotationNamed(TypeName("ext"))) {
          //  classTree = classTree.copy(name = TypeName(classTree.name.decoded + "$Ext")).copyPos(classTree).asInstanceOf[ClassDef]
          //}
          val oldInTrait = inTrait
          inTrait = true
          val tree2 = sup(classTree)
          inTrait = oldInTrait
          tree2.copyPos(tree)
        case tree@Select(o, TermName("hash")) if !inPat => q"$sireumZ(${transform(o)}.hashCode)".copyPos(tree)
        case Literal(Constant(true)) => q"$sireumT".copyPos(tree)
        case Literal(Constant(false)) => q"$sireumF".copyPos(tree)
        case Literal(Constant(_: Char)) =>
          (if (inPat) pq"$sireumCPat($tree)" else q"$sireumC($tree)").copyPos(tree)
        case Literal(Constant(_: Int)) =>
          (if (inPat) pq"$sireumZIntPat($tree)" else q"$sireumZ($tree)").copyPos(tree)
        case Literal(Constant(_: Long)) =>
          (if (inPat) pq"$sireumZLongPat($tree)" else q"$sireumZ($tree)").copyPos(tree)
        case Literal(Constant(_: Float)) =>
          (if (inPat) pq"$sireumF32Pat($tree)" else q"$sireumF32($tree)").copyPos(tree)
        case Literal(Constant(_: Double)) =>
          (if (inPat) pq"$sireumF64Pat($tree)" else q"$sireumF64($tree)").copyPos(tree)
        case Literal(Constant(_: String)) =>
          (if (inPat) pq"$sireumStringPat($tree)" else q"$sireumString($tree)").copyPos(tree)
        case q"$mods val $pat: $tpt = $rhs" =>
          if (!(rhs == EmptyTree || isDollar(rhs))) q"$mods val $pat: $tpt = ${assign(rhs)}".copyPos(tree) else tree
        case q"$mods var $pat: $tpt = $rhs" =>
          if (!(rhs == EmptyTree || isDollar(rhs))) q"$mods var $pat: $tpt = ${assign(rhs)}".copyPos(tree) else tree
        case tree: Assign => tree.copy(rhs = assign(tree.rhs)).copyPos(tree)
        case tree@Apply(Select(Ident(TermName(f)), TermName("update")), l) if !inPat && (f == "up" || f == "pat") =>
          tree.copy(args = l.dropRight(1) ++ l.takeRight(1).map(transform)).copyPos(tree)
        case q"$expr1(..$exprs2) = $expr" => q"${trans(expr1)}(..${exprs2.map(trans)}) = ${assign(expr)}".copyPos(tree)
        case tree: CaseDef =>
          val oldInPat = inPat
          inPat = true
          val pat = transform(tree.pat)
          inPat = oldInPat
          val g = transform(tree.guard)
          val b = transform(tree.body)
          if ((pat ne tree.pat) || (g ne tree.guard) || (b ne tree.body)) tree.copy(pat = pat, guard = g, body = b).copyPos(tree) else tree
        case q"(..$exprs)" if exprs.size > 1 => q"(..${exprs.map(assign)})".copyPos(tree)
        //case b: Block =>
        //  val b2 = sup(b)
        //  println(showCode(b2))
        //  b2
        //case tree: Apply if !inPat => transformApply(tree)
        case _ =>
          val tree2 = super.transform(tree)
          //        if (tree2 ne tree) {
          //          println(s"${tree2.pos.source.file.canonicalPath} [${tree2.pos.line}, ${tree2.pos.column}]: ${showCode(tree2)}")
          //        }
          tree2
      }
      r
    }
  }

  final class AnnotationTransformer(unit: CompilationUnit,
                                    var packageName: Vector[String],
                                    var enclosing: Vector[String]) extends TypingTransformer(unit) {

    val mat = new MetaAnnotationTransformer(new String(unit.source.content), Vector(),
      (offset, msg) => global.reporter.error(unit.position(offset), msg))

    {
      val errorOffset = mat.transform()
      if (errorOffset >= 0) {
        global.reporter.error(unit.position(errorOffset), s"Error processing compilation unit ${unit.source.file.canonicalPath}.")
      }
    }

    def parseTerms(terms: Seq[String]): List[Tree] = {
      val r = newUnitParser(terms.mkString(";\n")).parseStats
      r.foreach(erasePosition)
      r
    }

    def parseTypes(types: Seq[String]): List[Tree] = {
      val o = newUnitParser(s"object X extends Y with ${types.mkString(" with ")}").parseStats.
        head.asInstanceOf[ModuleDef]
      erasePosition(o)
      o.impl.parents.tail
    }

    def erasePosition(tree: Tree): Unit = {
      tree.pos = NoPosition
      for (t <- tree.children) {
        erasePosition(t)
      }
    }

    def ref2strings(tree: Any): Vector[String] = {
      tree match {
        case tree: Ident => Vector(tree.name.encoded)
        case tree: Select => ref2strings(tree.qualifier) :+ tree.name.encoded
      }
    }

    override def transform(tree: Tree): Tree = {
      val oldEnclosing = enclosing
      val tree2 = tree match {
        case q"package $ref { ..$stats }" =>
          packageName = ref2strings(ref)
          val newStats = companionStats(stats)
          if (stats ne newStats) tree.asInstanceOf[PackageDef].copy(stats = newStats) else tree
        case tree: ClassDef =>
          enclosing :+= tree.name.decoded
          var r = tree
          mat.classContructorVals.get(enclosing) match {
            case Some(ns) =>
              val names = ns.toSet
              val q"$mods class $tpname[..$tparams] $ctorMods(..$params) extends { ..$earlydefns } with ..$parents { $self => ..$stats }" = r
              var newStats = stats
              val newParams = for (p <- params) yield {
                p match {
                  case p: ValDef =>
                    val name = p.name.decoded
                    val uname = TermName(s"_$name")
                    newStats ::= q"def ${TermName(name)} = $uname".copyPos(p)
                    if (names.contains(name)) p.copy(name = uname) else p
                }
              }
              r = q"$mods class $tpname[..$tparams] $ctorMods(..$newParams) extends { ..$earlydefns } with ..$parents { $self => ..$newStats }".copyPosT(r)
            case _ =>
          }
          mat.classMembers.get(enclosing) match {
            case Some(members) =>
              r match {
                case q"$mods class $tpname[..$tparams] $ctorMods(...$paramss) extends { ..$earlydefns } with ..$parents { $self => ..$stats }" =>
                  val newStats = stats ++ parseTerms(members)
                  r = q"$mods class $tpname[..$tparams] $ctorMods(...$paramss) extends { ..$earlydefns } with ..$parents { $self => ..$newStats }".copyPosT(r)
                case q"$mods trait $tpname[..$tparams] extends { ..$earlydefns } with ..$parents { $self => ..$stats }" =>
                  val newStats = stats ++ parseTerms(members)
                  r = q"$mods trait $tpname[..$tparams] extends { ..$earlydefns } with ..$parents { $self => ..$newStats }".copyPosT(r)
              }
            case _ =>
          }
          mat.classSupers.get(enclosing) match {
            case Some(supers) => r = r.copy(impl = r.impl.copy(parents = r.impl.parents ++ parseTypes(supers)))
            case _ =>
          }
          r
        case tree: ModuleDef =>
          enclosing :+= tree.name.decoded
          var r = tree
          mat.companionMembers.get(enclosing) match {
            case Some(members) =>
              val q"$mods object $tname extends { ..$earlydefns } with ..$parents { $self => ..$stats }" = r
              val newStats = companionStats(objectStats(stats)) ++ parseTerms(members)
              r = q"$mods object $tname extends { ..$earlydefns } with ..$parents { $self => ..$newStats }".copyPosT(r)
            case _ =>
              val q"$mods object $tname extends { ..$earlydefns } with ..$parents { $self => ..$stats }" = r
              val newStats = companionStats(objectStats(stats))
              if (stats ne newStats) {
                r = q"$mods object $tname extends { ..$earlydefns } with ..$parents { $self => ..$newStats }".copyPosT(r)
              }
          }
          mat.companionSupers.get(enclosing) match {
            case Some(supers) => r = r.copy(impl = r.impl.copy(parents = r.impl.parents ++ parseTypes(supers)))
            case _ =>
          }
          r
        case tree: DefDef =>
          if (tree.mods.hasAnnotationNamed(TypeName("spec"))) EmptyTree else tree
        case tree: ValDef =>
          if (tree.mods.hasAnnotationNamed(TypeName("spec"))) EmptyTree else tree
        case _ => tree
      }
      val r = super.transform(tree2)
      enclosing = oldEnclosing
      r
    }

    def objectStats(stats: List[Tree]): List[Tree] = {
      for (stat <- stats) yield {
        val name = stat match {
          case stat: ValDef => stat.name.decoded
          case stat: DefDef => stat.name.decoded
          case stat: ClassDef => stat.name.decoded
          case stat: ModuleDef => stat.name.decoded
          case _ => ""
        }
        mat.objectMemberReplace.get(enclosing :+ name) match {
          case Some(text) => parseTerms(Vector(text)).head.copyPos(stat)
          case _ => stat
        }
      }
    }

    def companionStats(stats: List[Tree]): List[Tree] = {
      var newStats = List[Tree]()
      var hasChanged = false
      for (stat <- stats) {
        stat match {
          case stat: ClassDef =>
            val name = enclosing :+ stat.name.decoded
            if (mat.companionMembers.contains(name) &&
              !stats.exists({
                case md: ModuleDef =>
                  name == (enclosing :+ md.name.decoded)
                case _ => false
              })) {
              hasChanged = true
              newStats ::= q"object ${stat.name.toTermName} {}".copyPos(stat)
            } else {
            }
          case _ =>
        }
        newStats ::= stat
      }
      if (hasChanged) newStats.reverse else stats
    }

  }

  def newPhase(prev: Phase): StdPhase = new StdPhase(prev) {
    def apply(unit: CompilationUnit): Unit = {
      var isSireum = unit.source.file.hasExtension("slang") || unit.source.file.hasExtension("logika") ||
        (unit.source.file.hasExtension("sc") &&
          (unit.body.children.headOption match {
            case Some(x) if x == importSireum || x == importLogika => true
            case _ => false
          }))
      if (!isSireum) {
        val cs = unit.source.content
        val i = cs.indexOf('\n')
        val sb = new java.lang.StringBuilder
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
        val at = new AnnotationTransformer(unit, Vector(), Vector())
        //println("AT created")
        val st = new SemanticsTransformer(unit, inPat = false, inTrait = false)
        //println("ST created")
        val b1 = st.transform(unit.body)
        //println("ST transformation passed")
        val b2 = at.transform(b1)
        //println("AT transformation passed")
        val newBody = fixPos(b2)
        //println("fixpos passed")
        unit.body = newBody
        val dir = settings.outputDirs.outputDirFor(unit.source.file).file
        val filename = unit.source.file.file.getName
        val file = new java.io.File(dir, "transformed/" +
          (if (at.packageName.isEmpty) "" else at.packageName.mkString("/") + '/') + filename)
        file.getParentFile.mkdirs()
        val fw = new java.io.FileWriter(file)
        fw.write(showCode(unit.body))
        fw.close()
      }
    }
  }
}