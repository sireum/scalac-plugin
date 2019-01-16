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
import scala.collection.{Map => CMap}
import scala.collection.mutable.{Map => MMap}

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

  def tmatchQ = q"$sireumQ.helper.$$tmatch"

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
                                   var inNative: Boolean,
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

    def tmatch(tree: Tree): Tree =
      q"$tmatchQ($tree)".copyPos(tree)

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
          val oldInTrait = inTrait
          inTrait = true
          val tree2 = sup(classTree)
          inTrait = oldInTrait
          tree2.copyPos(tree)
        case tree@Select(o, TermName("hash")) if !inPat => q"$sireumZ(${transform(o)}.hashCode)".copyPos(tree)
        case Literal(Constant(true)) => q"$sireumT".copyPos(tree)
        case Literal(Constant(false)) => q"$sireumF".copyPos(tree)
        case Literal(Constant(_: Char)) =>
          (if (inPat)
            if (inNative) tree else pq"$sireumCPat($tree)"
          else q"$sireumC($tree)").copyPos(tree)
        case Literal(Constant(_: Int)) =>
          (if (inPat) pq"$sireumZIntPat($tree)" else q"$sireumZ($tree)").copyPos(tree)
        case Literal(Constant(_: Long)) =>
          (if (inPat) pq"$sireumZLongPat($tree)" else q"$sireumZ($tree)").copyPos(tree)
        case Literal(Constant(_: Float)) =>
          (if (inPat)
            if (inNative) tree else pq"$sireumF32Pat($tree)"
          else q"$sireumF32($tree)").copyPos(tree)
        case Literal(Constant(_: Double)) =>
          (if (inPat)
            if (inNative) tree else pq"$sireumF64Pat($tree)"
          else q"$sireumF64($tree)").copyPos(tree)
        case Literal(Constant(_: String)) =>
          (if (inPat)
            if (inNative) tree else pq"$sireumStringPat($tree)"
          else q"$sireumString($tree)").copyPos(tree)
        case q"$mods val $pat: $tpt = $rhs" =>
          if (!(rhs == EmptyTree || isDollar(rhs))) q"$mods val $pat: $tpt = ${assign(rhs)}".copyPos(tree) else tree
        case q"$mods var $pat: $tpt = $rhs" =>
          if (!(rhs == EmptyTree || isDollar(rhs))) q"$mods var $pat: $tpt = ${assign(rhs)}".copyPos(tree) else tree
        case tree: Assign => tree.copy(rhs = assign(tree.rhs)).copyPos(tree)
        case tree@Apply(Select(Ident(TermName(f)), TermName("update")), l) if !inPat && (f == "up" || f == "pat") =>
          tree.copy(args = l.dropRight(1) ++ l.takeRight(1).map(transform)).copyPos(tree)
        case q"$expr1(..$exprs2) = $expr" => q"${trans(expr1)}(..${exprs2.map(trans)}) = ${assign(expr)}".copyPos(tree)
        case tree: Match =>
          val oldInNative = inNative
          inNative = tree.selector match {
            case q"$_.native" => true
            case _ => false
          }
          val r = tree.copy(selector = tmatch(tree.selector), cases = tree.cases.map(transform).asInstanceOf[List[CaseDef]]).copyPos(tree)
          inNative = oldInNative
          r
        case tree: CaseDef =>
          val oldInPat = inPat
          inPat = true
          val pat = transform(tree.pat)
          inPat = oldInPat
          val g = transform(tree.guard)
          val b = transform(tree.body)
          if ((pat ne tree.pat) || (g ne tree.guard) || (b ne tree.body)) tree.copy(pat = pat, guard = g, body = b).copyPos(tree) else tree
        case q"(..$exprs)" if exprs.size > 1 => q"(..${exprs.map(assign)})".copyPos(tree)
        case tree: Return =>
          if (tree.expr == EmptyTree || tree == q"()") {
            return tree
          } else {
            tree.copy(expr = assign(tree.expr)).copyPos(tree)
          }
        case _ =>
          super.transform(tree)
      }
      r
    }
  }

  final class AnnotationTransformer(unit: CompilationUnit,
                                    var packageName: Vector[String],
                                    var enclosing: Vector[String]) extends TypingTransformer(unit) {

    val untraitMask: global.FlagSet = ~global.Flag.TRAIT
    val mat = new MetaAnnotationTransformer(new String(unit.source.content), Vector(),
      (offset, msg) => global.reporter.error(unit.position(offset), msg))
    val rwTree: MMap[Tree, Tree] = {
      import scala.collection.JavaConverters._
      new java.util.IdentityHashMap[Tree, Tree].asScala
    }

    val classParamMods: Modifiers = {
      val q"$_ class $_[..$_] $_(...$paramss)" = q"class A(x: Int)"
      val ps = paramss.head.asInstanceOf[List[ValDef]]
      ps.head.mods
    }

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
          val newStats = companionStats(rewriteStats(mat.objectMemberReplace, stats))
          if (stats ne newStats) tree.asInstanceOf[PackageDef].copy(stats = newStats).copyPosT(tree) else tree
        case tree: ClassDef =>
          enclosing :+= tree.name.decoded
          mat.classReplace.get(enclosing) match {
            case Some(text) =>
              enclosing = oldEnclosing
              return parseTerms(Vector(text)).head.copyPos(tree)
            case _ =>
          }
          var r = tree
          if (mat.adtTraits.contains(enclosing)) {
            r = r.copy(mods = r.mods | global.Flag.SEALED).copyPosT(r)
          }
          mat.classMembers.get(enclosing) match {
            case Some(members) =>
              r match {
                case q"$mods class $tpname[..$tparams] $ctorMods(...$paramss) extends { ..$earlydefns } with ..$parents { $self => ..$stats }" =>
                  val newStats = parseTerms(members) ++ rewriteStats(mat.classMemberReplace, stats)
                  val newParamss = paramss.map(_.map {
                    case p: ValDef => p.copy(mods = classParamMods, name = TermName(s"__${p.name.decoded}")).copyPosT(p.duplicate) // https://github.com/scala/bug/issues/8771
                  })
                  r = q"${r.mods | global.Flag.FINAL} class $tpname[..$tparams] $ctorMods(...$newParamss) extends { ..$earlydefns } with ..$parents { $self => ..$newStats }".copyPosT(r)
                case q"$mods trait $tpname[..$tparams] extends { ..$earlydefns } with ..$parents { $self => ..$stats }" =>
                  val newStats = parseTerms(members) ++ rewriteStats(mat.classMemberReplace, stats)
                  r = q"$mods trait $tpname[..$tparams] extends { ..$earlydefns } with ..$parents { $self => ..$newStats }".copyPosT(r)
              }
            case _ =>
          }
          mat.classSupers.get(enclosing) match {
            case Some(supers) => r = r.copy(impl = r.impl.copy(parents = r.impl.parents ++ parseTypes(supers)).copyPosT(r.impl)).copyPosT(r)
            case _ =>
          }
          r
        case tree: ModuleDef =>
          enclosing :+= tree.name.decoded
          var r = tree
          mat.objectMembers.get(enclosing) match {
            case Some(members) =>
              val newStats = companionStats(rewriteStats(mat.objectMemberReplace, r.impl.body)) ++ parseTerms(members)
              r = r.copy(impl = r.impl.copy(body = newStats).copyPosT(r.impl)).copyPosT(r)
            case _ =>
              val newStats = companionStats(rewriteStats(mat.objectMemberReplace, r.impl.body))
              if (r.impl.body ne newStats) r = r.copy(impl = r.impl.copy(body = newStats).copyPosT(r.impl)).copyPosT(r)
          }
          mat.objectSupers.get(enclosing) match {
            case Some(supers) =>
              r = r.copy(impl = r.impl.copy(parents = r.impl.parents ++ parseTypes(supers)).copyPosT(r.impl)).copyPosT(r)
            case _ =>
          }
          r
        case tree: DefDef =>
          if (tree.mods.hasAnnotationNamed(TypeName("spec"))) EmptyTree else tree
        case tree: ValDef =>
          if (tree.mods.hasAnnotationNamed(TypeName("spec"))) EmptyTree else tree
        case _ => tree
      }
      rwTree.get(tree2) match {
        case Some(r) =>
          rwTree -= tree2
          enclosing = oldEnclosing
          r
        case _ =>
          val r = super.transform(tree2)
          enclosing = oldEnclosing
          r
      }
    }

    def rewriteStats(rwMap: CMap[Vector[String], String], stats: List[Tree]): List[Tree] = {
      def rewriteBody(body: Tree, t: Tree): Unit = {
        t match {
          case Ident(TermName("$body$")) =>
            rwTree(t) = body
            return
          case _ =>
        }
        for (child <- t.children) {
          rewriteBody(body, child)
        }
      }

      for (stat <- stats) yield {
        val (name, body) = stat match {
          case stat: ValDef => (stat.name.decoded, stat.rhs)
          case stat: DefDef => (stat.name.decoded, stat.rhs)
          case stat: ClassDef => (stat.name.decoded, EmptyTree)
          case stat: ModuleDef => (stat.name.decoded, EmptyTree)
          case _ => ("", EmptyTree)
        }
        rwMap.get(enclosing :+ name) match {
          case Some(text) =>
            val r = parseTerms(Vector(text)).head.copyPos(stat)
            if (body != EmptyTree && text.contains("$body$")) {
              rewriteBody(body, r)
            }
            r
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
            if (mat.objectMembers.contains(name) &&
              !stats.exists({
                case md: ModuleDef =>
                  name == (enclosing :+ md.name.decoded)
                case _ => false
              })) {
              hasChanged = true
              val o = q"object ${stat.name.toTermName} {}"
              o.pos = stat.pos.makeTransparent
              newStats ::= o
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
        val st = new SemanticsTransformer(unit, inNative = false, inPat = false, inTrait = false)
        val b1 = st.transform(unit.body)
        val b2 = at.transform(b1)
        val newBody = fixPos(b2)
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