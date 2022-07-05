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

import scala.meta._
import MetaAnnotationTransformer._
import scala.collection.mutable.{ArrayBuffer => MSeq}

class RangeTransformer(mat: MetaAnnotationTransformer) {
  def transform(name: Vector[String], tree: Tree, args: List[Term]): Unit = {
    def unsupported(op: Predef.String) = Lit.String(s"Unsupported $name operation '$op'")

    tree match {
      case tree: Defn.Class =>
        val tname = tree.name
        var minOpt: Option[BigInt] = None
        var maxOpt: Option[BigInt] = None
        var indexB = false
        for (arg <- args) {
          arg match {
            case q"min = ${exp: Term}" =>
              extractInt(exp) match {
                case Some(n) => minOpt = scala.Some(n)
                case _ =>
                  mat.error(arg.pos, s"Invalid Slang @range ${tname.value} min argument: ${arg.syntax}")
                  return
              }
            case q"max = ${exp: Term}" =>
              extractInt(exp) match {
                case Some(n) => maxOpt = scala.Some(n)
                case _ =>
                  mat.error(arg.pos, s"Invalid Slang @range ${tname.value} max argument: ${arg.syntax}")
                  return
              }
            case q"index = ${exp: Term}" =>
              extractBoolean(exp) match {
                case Some(b) => indexB = b
                case _ =>
                  mat.error(arg.pos, s"Invalid Slang @range ${tname.value} index argument: ${arg.syntax}")
                  return
              }
            case _ =>
              mat.error(arg.pos, s"Invalid Slang @range ${tname.value} argument: ${arg.syntax}")
              return
          }
        }
        val index = (minOpt, maxOpt) match {
          case (Some(n), Some(m)) =>
            if (n > m) {
              mat.error(tree.pos, s"Slang @range ${tname.value}'s min ($n) should not be greater than its max ($m).")
              return
            }
            if (indexB) n else BigInt(0)
          case (Some(n), _) =>
            if (indexB) n else BigInt(0)
          case (_, Some(_)) =>
            if (indexB) {
              mat.error(tree.pos, s"Slang @range ${tname.value}'s min should specified when index is enabled.")
            } else BigInt(0)
          case _ => mat.error(tree.pos, s"Slang @range ${tname.value} should have either a minimum, a maximum, or both.")
        }

        val cname = tname.value
        val typeName = Type.Name(cname)
        val termName = Term.Name(cname)
        val iTermName = zCompanionName(cname)
        val lowerTermName = scPrefix(cname)
        val ctorName = Type.Name(cname)
        val nameStr = Lit.String(cname)
        val signed = minOpt.forall(_ < 0)
        val scTypeName = scName(cname)
        val (boxerTerm, boxerObject) = (minOpt, maxOpt) match {
          case (Some(min: BigInt), Some(max: BigInt)) =>
            if (scala.Byte.MinValue.toInt <= min && max.toInt <= scala.Byte.MaxValue)
              (q"$termName.Boxer", List[Stat](
                q"""object Boxer extends _root_.org.sireum.Z.Boxer.Byte {
                  def make(o: $scalaByte): $typeName = $termName($sireumZQ.MP(o))
                }"""))
            else if (scala.Short.MinValue.toInt <= min && max.toInt <= scala.Short.MaxValue)
              (q"$termName.Boxer", List[Stat](
                q"""object Boxer extends _root_.org.sireum.Z.Boxer.Short {
                  def make(o: $scalaShort): $typeName = $termName($sireumZQ.MP(o))
                }"""))
            else if (scala.Int.MinValue <= min && max <= scala.Int.MaxValue)
              (q"$termName.Boxer", List[Stat](
                q"""object Boxer extends _root_.org.sireum.Z.Boxer.Int {
                  def make(o: $scalaInt): $typeName = $termName($sireumZQ.MP(o))
                }"""))
            else if (scala.Long.MinValue <= min && max <= scala.Long.MaxValue)
              (q"$termName.Boxer", List[Stat](
                q"""object Boxer extends _root_.org.sireum.Z.Boxer.Long {
                  def make(o: $scalaLong): $typeName = $termName($sireumZQ.MP(o))
                }"""))
            else (q"$sireumZQ.Boxer.Z", List[Stat]())
          case _ => (q"$sireumZQ.Boxer.Z", List[Stat]())
        }

        def min = Lit.String(minOpt.map(_.toString).getOrElse("0"))

        def max = Lit.String(maxOpt.map(_.toString).getOrElse("0"))

        val isZeroIndex = Lit.Boolean(index == 0)

        val minUnsupported = unsupported("Min")
        val maxUnsupported = unsupported("Max")
        val minErrorMessage = Lit.String(s" is less than $cname.Min (${min.value})")
        val maxErrorMessage = Lit.String(s" is greater than $cname.Max (${max.value})")

        mat.classReplace(name) =
          if (mat.isScript)
            q"""class $typeName(val value: $sireumZ) extends _root_.org.sireum.Z.Range[$typeName] {
                  @inline def Name: $javaString = $termName.Name
                  @inline def Min: $typeName = $termName.Min
                  @inline def Max: $typeName = $termName.Max
                  @inline def Index: $typeName = $termName.Index
                  @inline def isZeroIndex: $scalaBoolean = $termName.isZeroIndex
                  @inline def isSigned: $scalaBoolean = $termName.isSigned
                  @inline def hasMin: $scalaBoolean = $termName.hasMin
                  @inline def hasMax: $scalaBoolean = $termName.hasMax
                  @inline def ===(that: $typeName): $sireumB = value == that.value
                  @inline def =!=(that: $typeName): $sireumB = value != that.value
                  def make(v: $sireumZ): $typeName = $termName(v)
                  def boxer = $boxerTerm
                  override def equals(that: $scalaAny): $scalaBoolean =
                    that match {
                      case that: $typeName => value == that.value
                      case _ => false
                    }
                  override def hashCode: $scalaInt = value.hashCode
                }""".syntax
          else
            q"""final class $typeName(val value: $sireumZ) extends _root_.scala.AnyVal with _root_.org.sireum.Z.Range[$typeName] {
                  @inline def Name: $javaString = $termName.Name
                  @inline def Min: $typeName = $termName.Min
                  @inline def Max: $typeName = $termName.Max
                  @inline def Index: $typeName = $termName.Index
                  @inline def isZeroIndex: $scalaBoolean = $termName.isZeroIndex
                  @inline def isSigned: $scalaBoolean = $termName.isSigned
                  @inline def hasMin: $scalaBoolean = $termName.hasMin
                  @inline def hasMax: $scalaBoolean = $termName.hasMax
                  @inline def ===(that: $typeName): $sireumB = value == that.value
                  @inline def =!=(that: $typeName): $sireumB = value != that.value
                  def make(v: $sireumZ): $typeName = $termName(v)
                  def boxer = $boxerTerm
                }""".syntax

        val objectMembers = (Seq(
          q"val Name: $javaString = $nameStr",
          q"lazy val Min: $typeName = if (hasMin) new $ctorName($sireumZQ.MP($min)) else halt($minUnsupported)",
          q"lazy val Max: $typeName = if (hasMax) new $ctorName($sireumZQ.MP($max)) else halt($maxUnsupported)",
          q"val Index: $typeName = new $ctorName($sireumZQ.MP(${Lit.String(index.toString)}))",
          q"val isZeroIndex: $scalaBoolean = $isZeroIndex",
          q"val isSigned: $scalaBoolean = ${Lit.Boolean(signed)}",
          q"val isBitVector: $scalaBoolean = false",
          q"val hasMin: $scalaBoolean = ${Lit.Boolean(minOpt.nonEmpty)}",
          q"val hasMax: $scalaBoolean = ${Lit.Boolean(maxOpt.nonEmpty)}",
          q"""def BitWidth: $scalaInt = halt(s"Unsupported $$Name operation 'BitWidth'")""",
          q"""def random: $typeName = if (hasMax && hasMin) {
                val d = Max.value - Min.value + $sireumZQ.MP.one
                val n = $sireumZQ.random % d
                $termName(n + Min.value)
              } else if (hasMax) {
                val n = $sireumZQ.random
                $termName(if (n > Max.value) Max.value - n else n)
              } else {
                val n = $sireumZQ.random
                $termName(if (n < Min.value) Min.value + n else n)
              }""",
          q"""def randomSeed(seed: $sireumZ): $typeName = if (hasMax && hasMin) {
                val d = Max.value - Min.value + $sireumZQ.MP.one
                val n = $sireumZQ.randomSeed(seed) % d
                $termName(n + Min.value)
              } else if (hasMax) {
                val n = $sireumZQ.randomSeed(seed)
                $termName(if (n > Max.value) Max.value - n else n)
              } else {
                val n = $sireumZQ.randomSeed(seed)
                $termName(if (n < Min.value) Min.value + n else n)
              }""",
          q"""private def check(v: $sireumZ): $sireumZ = {
                if (hasMin) assert(Min.value <= v, v.toString + $minErrorMessage)
                if (hasMax) assert(v <= Max.value, v.toString + $maxErrorMessage)
                v
              }""",
          q"def apply(n: $scalaInt): $typeName = Int(n)",
          q"def apply(n: $scalaLong): $typeName = Long(n)",
          q"def apply(n: $sireumZ): $typeName = new $ctorName(check(n))",
          q"def apply(s: $sireumString): $sireumOption[$typeName] = try $sireumSomeQ($termName.$$String(s.value)) catch { case _: _root_.java.lang.Throwable => $sireumNoneQ[$typeName]() }",
          q"def unapply(n: $typeName): $scalaOption[$sireumZ] = $scalaSomeQ(n.value)",
          q"""object Int extends _root_.org.sireum.$$ZCompanionInt[$typeName] {
                def apply(n: $scalaInt): $typeName = $termName($sireumZQ.MP(n))
                def unapply(n: $typeName): $scalaOption[$scalaInt] =
                  if ($scalaIntQ.MinValue <= n.value && n.value <= $scalaIntQ.MaxValue) $scalaSomeQ(n.value.toBigInt.toInt)
                  else $scalaNoneQ
              }""",
          q"""object Long extends _root_.org.sireum.$$ZCompanionLong[$typeName] {
                def apply(n: $scalaLong): $typeName = $termName($sireumZQ.MP(n))
                def unapply(n: $typeName): $scalaOption[$scalaLong] =
                  if ($scalaLongQ.MinValue <= n.value && n.value <= $scalaLongQ.MaxValue) $scalaSomeQ(n.value.toBigInt.toLong)
                  else $scalaNoneQ
              }""",
          q"""object $$String extends _root_.org.sireum.$$ZCompanionString[$typeName] {
                def apply(s: $javaString): $typeName = BigInt($sireumZQ.$$String(s).toBigInt)
                def unapply(n: $typeName): $scalaOption[$javaString] = $scalaSomeQ(n.toBigInt.toString)
              }""",
          q"""object BigInt extends _root_.org.sireum.$$ZCompanionBigInt[$typeName] {
                def apply(n: $scalaBigInt): $typeName = $termName($sireumZQ.MP(n))
                def unapply(n: $typeName): $scalaOption[$scalaBigInt] = $scalaSomeQ(n.toBigInt)
              }""",
          q"""implicit class $scTypeName(val sc: _root_.scala.StringContext) {
                object $lowerTermName {
                  def apply(args: $scalaAny*): $typeName = {
                    assume(args.isEmpty && sc.parts.length == 1)
                    $$String(sc.parts.head)
                  }
                  def unapply(n: $typeName): $scalaBoolean = {
                    assume(sc.parts.length == 1)
                    n == $$String(sc.parts.head)
                  }
                }
              }""",
          q"implicit val $iTermName: _root_.org.sireum.$$ZCompanion[$typeName] = this"
        ) ++ boxerObject).map(_.syntax)
        mat.objectMembers.getOrElseUpdate(name, MSeq()) ++= objectMembers
        mat.objectSupers.getOrElseUpdate(name, MSeq()) += t"_root_.org.sireum.$$ZCompanion[$typeName]".syntax
      case _ => mat.error(tree.pos, s"Invalid Slang @range on: ${tree.syntax}")
    }
  }
}
