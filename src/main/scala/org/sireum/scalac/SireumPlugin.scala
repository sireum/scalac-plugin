/*
 Copyright (c) 2019, Robby, Kansas State University
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
import scala.reflect.internal.ModifierFlags
import scala.collection.Seq
import scala.reflect.internal.Reporter

object SireumPlugin {

  val implicationOps: Set[String] = Set("->:", "-->:", "imply_:", "simply_:")

  def isSireum(global: Global)(unit: global.CompilationUnit): Boolean = {
    var r = unit.source.file.hasExtension("slang") || unit.source.file.hasExtension("logika")
    if (!r) {
      val cs = unit.source.content.clone
      if (unit.source.file.hasExtension("cmd") && cs.startsWith("::/*#!".toCharArray)) {
        val suffix = "::!#*/"
        for (i <- 0 until cs.indexOfSlice(suffix.toCharArray) + suffix.length) {
          cs(i) = ' '
        }
      }
      val sb = new java.lang.StringBuilder
      var i = if (unit.source.file.hasExtension("cmd") && cs.startsWith("::/*#!".toCharArray)) {
        val suffix = "::!#*/"
        cs.indexOfSlice(suffix.toCharArray) + suffix.length
      } else 0
      while (i < cs.length && cs(i).isWhitespace) i += 1
      var found = false
      while (i < cs.length && !found) {
        cs(i) match {
          case '\n' => found = true
          case c => if (!c.isWhitespace) sb.append(c)
        }
        i += 1
      }
      val firstLine = sb.toString
      r = firstLine.contains("#Sireum")
    }
    r
  }

  def eval[T](exp: String): T = {
    import scala.tools.reflect.ToolBox
    import scala.reflect.runtime.universe
    val tb = universe.runtimeMirror(getClass.getClassLoader).mkToolBox()
    tb.eval(tb.parse(exp)).asInstanceOf[T]
  }
}

class SireumPlugin(override val global: Global) extends Plugin {
  override val name = "sireum"
  override val description = "Compiler plugin for the Sireum Scala subset."
  override val components: List[PluginComponent] = List(
    new SireumComponent(global), new SireumContractEraserComponent(global)
  )

  val originalReporter: scala.tools.nsc.reporters.FilteringReporter = global.reporter

  global.reporter = new scala.tools.nsc.reporters.FilteringReporter {

    val suppressedWarnings: Set[String] = Set(
      "symbol literal is deprecated",
      "The outer reference in this type test cannot be checked at run time",
    )

    override def filter(pos: scala.reflect.internal.util.Position, msg: String, severity: Severity): Int = {
      if (suppressedWarnings.exists(m => msg.contains(m))) return Reporter.Suppress
      if (msg.startsWith("match may not be exhaustive")) {
        val text = pos.lineContent.trim
        if ((text.startsWith("val") || text.startsWith("var")) && !text.contains("match")) {
          return Reporter.Suppress
        }
      }
      super.filter(pos, msg, severity)
    }

    override def doReport(pos: scala.reflect.internal.util.Position, msg: String, severity: Severity): Unit = {
      severity match {
        case INFO => originalReporter.echo(pos, msg)
        case WARNING => originalReporter.warning(pos, msg)
        case _ => originalReporter.error(pos, msg)
      }
    }

    override def settings: scala.tools.nsc.Settings = originalReporter.settings
  }
}

final class SireumComponent(val global: Global) extends PluginComponent with TypingTransformers {

  import global._

  override val phaseName = "sireum"
  override val runsRightAfter: Option[String] = Some("parser")
  override val runsAfter: List[String] = runsRightAfter.toList
  override val runsBefore: List[String] = List[String]("namer")

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

  def retQ = q"$sireumQ.helper.$$ret"

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

    def retNoTrans(tree: Tree): Tree =
      if (inPat) tree else q"$retQ($tree)".copyPos(tree)

    def ret(tree: Any): Tree = tree match {
      case _: Literal => trans(tree)
      case _: Function => trans(tree)
      case Apply(Select(Apply(Ident(TermName("StringContext")), _), _), _) => trans(tree)
      case _ => retNoTrans(trans(tree))
    }

    def tmatch(tree: Tree): Tree =
      q"$tmatchQ(${transform(tree)})".copyPos(tree)

    def pos(tree: Any): Position = tree.asInstanceOf[Tree].pos

    override def transform(tree: Tree): Tree = {
      val r = tree match {
        case tree: DefDef =>
          tree.rhs match {
            case rhs@Apply(sc@Select(Apply(Ident(TermName("StringContext")), _), TermName("l")), _) =>
              global.reporter.error(rhs.pos, "[Slang] l\"\"\"...\"\"\" is deprecated, please use Slang Code Contract spec.")
              tree
            case q"Contract.Only(..$_)" => tree.copy(rhs = EmptyTree).copyPosT(tree)
            case _ =>
              sup(tree)
          }
        case tree@Apply(sc@Select(Apply(Ident(TermName("StringContext")), _), TermName("l")), _) if !inPat =>
          global.reporter.error(tree.pos, "[Slang] l\"\"\"...\"\"\" is deprecated, please use Slang Code Contract spec.")
          tree
        case tree@Apply(Select(Apply(Ident(TermName("StringContext")), _), TermName("s")), _) if !inPat =>
          q"$sireumString(${sup(tree)})".copyPosT(tree)
        case tree@Apply(Select(Ident(TermName("scala")), TermName("Symbol")), _) => tree
        case tree@Apply(Ident(TermName("StringContext")), _) => tree
        case tree@q"$_ == $_" => q"$sireumQ.B(${sup(tree)})".copyPosT(tree)
        case tree@q"$_ != $_" => q"$sireumQ.B(${sup(tree)})".copyPosT(tree)
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
        case tree: ValDef if !(tree.rhs == EmptyTree || isDollar(tree.rhs)) =>
          tree.copy(rhs = assign(tree.rhs)).copyPos(tree)
        case tree: Assign => tree.copy(rhs = assign(tree.rhs)).copyPos(tree)
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
        case tree: Function if tree.vparams.forall(_.tpt.nonEmpty) =>
          if (tree.vparams.isEmpty && (tree.body == EmptyTree || tree.body == q"()")) {
            return tree
          } else {
            tree.copy(body = ret(tree.body)).copyPos(tree)
          }
        case tree: Return =>
          if (tree.expr == EmptyTree || tree == q"()") {
            return tree
          } else {
            tree.copy(expr = ret(tree.expr)).copyPos(tree)
          }
        case _ => super.transform(tree)
      }
      r
    }
  }

  final class AnnotationTransformer(unit: CompilationUnit,
                                    var packageName: Vector[String],
                                    var enclosing: Vector[String]) extends TypingTransformer(unit) {

    val mat = new MetaAnnotationTransformer({
      val name = unit.source.file.name
      !name.endsWith(".scala")
    }, new String(unit.source.content), Vector(),
      (offset, msg) => global.reporter.error(unit.position(offset), s"[Slang] $msg"))
    val rwTree: MMap[Tree, Tree] = {
      import scala.jdk.CollectionConverters._
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
        global.reporter.error(unit.position(errorOffset), s"[Slang] Error processing compilation unit ${unit.source.file.canonicalPath}.")
      }
    }

    def parseTerms(terms: Seq[String]): List[Tree] = {
      val r = newUnitParser(terms.mkString(";\n")).parseStats()
      r.foreach(erasePosition)
      r
    }

    def parseTypes(types: Seq[String]): List[Tree] = {
      val o = newUnitParser(s"object X extends Y with ${types.mkString(" with ")}").parseStats().
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
        case q"{ $_ val $x1 = $e1; $e2.${op: Name}($x2) }" if SireumPlugin.implicationOps.contains(op.decodedName.toString) =>
          val q"{ $s1; $s2 }" = tree
          val newS2 = q"$x2.$op($e2)".copyPos(s2)
          q"{ $s1; $newS2 }".copyPos(tree)
        case q"package $ref { ..$stats }" =>
          packageName = ref2strings(ref)
          val newStats = companionStats(rewriteStats(mat.objectMemberReplace, stats))
          if (stats ne newStats) tree.asInstanceOf[PackageDef].copy(stats = newStats).copyPosT(tree) else tree
        case tree: ClassDef =>
          val tree2: ClassDef = if (ignoreClass(tree)) {
            val stats = tree.impl.body
            val newStats = companionStats(rewriteStats(mat.objectMemberReplace, stats))
            if (stats ne newStats) tree.copy(impl = tree.impl.copy(body = newStats).copyPosT(tree.impl)).copyPosT(tree)
            else tree
          } else {
            enclosing :+= tree.name.decoded
            tree
          }
          mat.classReplace.get(enclosing) match {
            case Some(text) =>
              enclosing = oldEnclosing
              return parseTerms(Vector(text)).head.copyPos(tree2)
            case _ =>
          }
          var r = tree2
          if (mat.adtTraits.contains(enclosing)) {
            r = r.copy(mods = r.mods | global.Flag.SEALED).copyPosT(r)
          } else if (mat.adtClasses.contains(enclosing)) {
            r = r.copy(mods = r.mods | global.Flag.FINAL).copyPosT(r)
          }
          mat.classMembers.get(enclosing) match {
            case Some(members) =>
              r match {
                case q"$_ class $tpname[..$tparams] $ctorMods(...$paramss) extends { ..$earlydefns } with ..$parents { $self => ..$stats }" =>
                  val newStats = parseTerms(members) ++ rewriteStats(mat.classMemberReplace, stats)
                  val newParamss = paramss.asInstanceOf[Seq[Seq[Any]]].map(_.map {
                    case p: ValDef => p.copy(mods = classParamMods, name = TermName(s"__${p.name.decoded}")).copyPosT(p.duplicate) // HACK: https://github.com/scala/bug/issues/8771
                  })
                  val mods = if (mat.isScript) r.mods else r.mods | global.Flag.FINAL // HACK: https://github.com/scala/bug/issues/4440
                  r = q"$mods class $tpname[..$tparams] $ctorMods(...$newParamss) extends { ..$earlydefns } with ..$parents { $self => ..$newStats }".copyPosT(r)
                case q"$mods trait $tpname[..$tparams] extends { ..$earlydefns } with ..$parents { $self => ..$stats }" =>
                  val newStats = parseTerms(members) ++ rewriteStats(mat.classMemberReplace, stats)
                  r = q"$mods trait $tpname[..$tparams] extends { ..$earlydefns } with ..$parents { $self => ..$newStats }".copyPosT(r)
                case _ =>
                  var text = new String(r.pos.source.content.slice(r.pos.start, r.pos.end))
                  val i = text.indexOf('\n')
                  if (i > 0) {
                    text = text.substring(0, i) + "..."
                  }
                  global.reporter.error(r.pos, s"[Slang] Invalid class definition in Slang: '$text'.")
              }
            case _ =>
          }
          mat.classSupers.get(enclosing) match {
            case Some(supers) => r = r.copy(impl = r.impl.copy(parents = r.impl.parents ++ parseTypes(supers)).copyPosT(r.impl)).copyPosT(r)
            case _ =>
          }
          r
        case tree: ModuleDef =>
          var r = if (scriptObject(tree)) {
            val stats = tree.impl.body
            val main = stats(1).asInstanceOf[DefDef]
            val block = main.rhs.asInstanceOf[Block]
            val cls = block.stats.head.asInstanceOf[ClassDef]
            val argsStmt = fixPos(q"_root_.org.sireum.App.args = _root_.org.sireum.ISZ(args.map(s => _root_.org.sireum.String(s.trim)).toIndexedSeq: _*)".copyPosT(cls.impl))
            val rest = cls.impl.body.tail.head match {
              case Ident(TermName("$colon$colon")) if unit.source.file.hasExtension("cmd") => cls.impl.body.tail.tail
              case _ => cls.impl.body.tail
            }
            val newImpl = cls.impl.copy(body = cls.impl.body.head :: argsStmt :: rest).copyPosT(cls.impl)
            val newCls = cls.copy(impl = newImpl).copyPosT(cls)
            val newMain = main.copy(rhs = block.copy(stats =
              newCls :: block.stats.tail).copyPosT(block)).copyPosT(main.rhs)
            tree.copy(impl = tree.impl.copy(body = stats.head :: newMain :: stats.tail.tail).copyPosT(tree.impl)).copyPosT(tree)
          } else {
            enclosing :+= tree.name.decoded
            tree
          }
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
        case tree: ValDef =>
          if (tree.mods.hasAnnotationNamed(TypeName("spec")) && isDollar(tree.rhs))
            if (tree.mods.hasFlag(ModifierFlags.MUTABLE)) tree.copy(rhs = EmptyTree).copyPosT(tree)
            else tree.copy(mods = tree.mods | ModifierFlags.LAZY).copyPosT(tree)
          else tree
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

    def rewriteStats(rwMap: CMap[Vector[String], String], stats: Seq[Any]): Seq[Tree] = {
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
          case _ => stat.asInstanceOf[Tree]
        }
      }
    }

    def companionStats(stats: Seq[Tree]): List[Tree] = {
      var newStats = List[Tree]()
      var hasChanged = false
      for (stat <- stats) {
        stat match {
          case stat: ClassDef =>
            val name = enclosing :+ stat.name.decoded
            if (mat.objectMembers.contains(name) &&
              !stats.exists({
                case md: ModuleDef => name == enclosing :+ md.name.decoded
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
      if (hasChanged) newStats.reverse else stats.toList
    }

    def ignoreClass(tree: ClassDef): Boolean = "$anon" == tree.name.decoded

    def scriptObject(tree: ModuleDef): Boolean = "Main" == tree.name.decoded && {
      val stats = tree.impl.body
      if (stats.size == 2) {
        stats.head match {
          case q"def ${init: TermName}() = $_" if init.decoded == "<init>" =>
            stats(1) match {
              case q"def main(args: Array[String]): scala.Unit = $_" => true
              case _ => false
            }
          case _ => false
        }
      } else false
    }
  }

  final class CCTransformer(unit: CompilationUnit) extends TypingTransformer(unit) {

    def pred(trees: List[Tree]): Boolean =
      trees.exists({
        case q"###($_) { ..$_ }" => true
        case _ => false
      })

    def cc(tree: Tree): List[Tree] = tree match {
      case q"###($exp) { ..$stats }" =>
        if (SireumPlugin.eval[Boolean](showCode(exp.asInstanceOf[global.Tree])))
          stats.asInstanceOf[List[global.Tree]]
        else List()
      case _ => List(transform(tree))
    }

    override def transform(tree: Tree): Tree = {
      tree match {
        case tree: ModuleDef if pred(tree.impl.body) =>
          tree.copy(impl = tree.impl.copy(body =
            for (stat <- tree.impl.body; s <- cc(stat)) yield s).copyPosT(tree.impl)).copyPosT(tree)
        case tree: ClassDef if pred(tree.impl.body) =>
          tree.copy(impl = tree.impl.copy(body =
            for (stat <- tree.impl.body; s <- cc(stat)) yield s).copyPosT(tree.impl)).copyPosT(tree)
        case tree: Block if pred(tree.stats) =>
          val l = (for (stat <- tree.stats; s <- cc(stat)) yield s) ++ cc(tree.expr)
          Block(l.take(l.size - 1), l.last).copyPosT(tree)
        case _ => super.transform(tree)
      }
    }
  }

  final class IndexTransformer(unit: CompilationUnit) extends TypingTransformer(unit) {

    override def transform(tree: Tree): Tree = {
      tree match {
        case tree: TypeDef =>
          for (ann <- tree.mods.annotations) {
            ann match {
              case q"new index()" => return tree.copy(rhs = TypeBoundsTree(EmptyTree, tq"org.sireum.ZLike[${tree.name}]")).copyPos(tree)
              case _ =>
            }
          }
        case _ =>
      }
      super.transform(tree)
    }
  }

  def newPhase(prev: Phase): StdPhase = new StdPhase(prev) {
    def apply(unit: CompilationUnit): Unit = {
      if (unit.source.content.indexOfSlice(Array('#', '#', '#')) >= 0) {
        val cct = new CCTransformer(unit)
        unit.body = cct.transform(unit.body)
      }
      if (SireumPlugin.isSireum(global)(unit)) {
        val st = new SemanticsTransformer(unit, inNative = false, inPat = false, inTrait = false)
        val at = new AnnotationTransformer(unit, Vector(), Vector())
        val b1 = st.transform(unit.body)
        val b2 = at.transform(b1)
        val newBody = fixPos(b2)
        unit.body = newBody
        val dir = settings.outputDirs.outputDirFor(unit.source.file).file
        if (!dir.toURI.toASCIIString.contains(".jar/") && "true" == System.getenv("SIREUM_TRANSFORMED")) {
          val filename = unit.source.file.file.getName
          val file = new java.io.File(dir, "transformed/" +
            (if (at.packageName.isEmpty) "" else at.packageName.mkString("/") + '/') + filename)
          file.getParentFile.mkdirs()
          val fw = new java.io.FileWriter(file)
          fw.write(showCode(unit.body))
          fw.close()
        }
      }
      unit.body = new IndexTransformer(unit).transform(unit.body)
    }
  }
}

final class SireumContractEraserComponent(val global: Global) extends PluginComponent with TypingTransformers {

  import global._

  override val phaseName = "sireum-contract"
  override val runsAfter: List[String] = List[String]("typer")
  override val runsBefore: List[String] = List[String]("patmat")

  def isDollar(t: Any): Boolean = t match {
    case q"$$" => true
    case _ => false
  }

  final class SemanticsTransformer(unit: CompilationUnit) extends TypingTransformer(unit) {
    override def transform(tree: Tree): Tree = {
      tree match {
        case tree: DefDef =>
          tree.rhs match {
            case q"Contract.Only(..$_)" =>
              val tree2 = tree.copy(rhs = EmptyTree)
              tree2.pos = tree.pos
              tree2
            case _ => tree
          }
        case tree: ValDef if (tree.mods.hasAnnotationNamed(TypeName("spec")) && !isDollar(tree.rhs)) =>
          val r = q";"
          r.pos = tree.pos
          r
        case _ => tree
      }
    }
  }

  def newPhase(prev: Phase): StdPhase = new StdPhase(prev) {
    def apply(unit: CompilationUnit): Unit = {
      if (SireumPlugin.isSireum(global)(unit)) {
        val st = new SemanticsTransformer(unit)
        unit.body = st.transform(unit.body)
      }
    }
  }
}

