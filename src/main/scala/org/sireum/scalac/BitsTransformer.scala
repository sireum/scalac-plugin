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

class BitsTransformer(mat: MetaAnnotationTransformer) {
  def transform(name: Vector[String], tree: Tree, args: List[Term]): Unit = {
    def unsupported(op: Predef.String) = Lit.String(s"Unsupported $name operation '$op'")

    tree match {
      case tree: Defn.Class =>
        var widthOpt: Option[Int] = None
        var signedOpt: Option[Boolean] = None
        var indexB = false
        var minOpt: Option[BigInt] = None
        var maxOpt: Option[BigInt] = None
        val bi8 = BigInt(8)
        val bi16 = BigInt(16)
        val bi32 = BigInt(32)
        val bi64 = BigInt(64)
        for (arg <- args) {
          arg match {
            case q"signed = ${exp: Term}" =>
              extractBoolean(exp) match {
                case Some(b) => signedOpt = Some(b)
                case _ =>
                  mat.error(arg.pos, s"Invalid Slang @bits signed argument: ${arg.syntax}")
                  return
              }
            case q"width = ${exp: Term}" =>
              val nOpt = extractInt(exp)
              nOpt match {
                case Some(`bi8`) | Some(`bi16`) | Some(`bi32`) | Some(`bi64`) => widthOpt = Some(nOpt.get.toInt)
                case _ =>
                  mat.error(arg.pos, s"Invalid Slang @bits width argument: ${arg.syntax} (only 8, 16, 32, or 64 are currently supported)")
                  return
              }
            case q"min = ${exp: Term}" => minOpt = extractInt(exp)
            case q"max = ${exp: Term}" => maxOpt = extractInt(exp)
            case q"index = ${exp: Term}" =>
              extractBoolean(exp) match {
                case Some(b) => indexB = b
                case _ =>
                  mat.error(arg.pos, s"Invalid Slang @bits index argument: ${arg.syntax}")
                  return
              }
            case _ =>
              mat.error(arg.pos, s"Invalid Slang @bits argument: ${arg.syntax}")
              return
          }
        }
        val signed = signedOpt match {
          case Some(x) => x
          case _ => minOpt match {
            case Some(min) => min < 0
            case _ => true
          }
        }
        val width = widthOpt match {
          case Some(w) => w
          case _ => (minOpt, maxOpt) match {
            case (Some(min), Some(max)) =>
              if (signed) {
                if (Byte.MinValue.toInt <= min && max <= Byte.MaxValue.toInt) 8
                else if (Short.MinValue.toInt <= min && max <= Short.MaxValue.toInt) 16
                else if (Int.MinValue <= min && max <= Int.MaxValue) 32
                else if (Long.MinValue <= min && max <= Long.MaxValue) 64
                else {
                  mat.error(tree.pos, s"Invalid Slang @bits: min/max do not fit into signed integer 8, 16, 32, or 64 bits.")
                  return
                }
              } else {
                if (0 <= min && max <= Byte.MaxValue.toInt - Byte.MinValue.toInt) 8
                else if (0 <= min && max <= Short.MaxValue.toInt - Short.MinValue.toInt) 16
                else if (0 <= min && max <= Int.MaxValue.toLong - Int.MinValue.toLong) 32
                else if (0 <= min && max <= BigInt(Long.MaxValue) - BigInt(Long.MinValue)) 64
                else {
                  mat.error(tree.pos, s"Invalid Slang @bits: min/max do not fit into unsigned integer 8, 16, 32, or 64 bits.")
                  return
                }
              }
            case _ =>
              mat.error(tree.pos, s"Slang @bits ${tree.name.value} requires either width or min/max to be specified.")
              return
          }
        }
        val (wMin, wMax) =
          if (signed) (BigInt(-2).pow(width - 1), BigInt(2).pow(width - 1) - 1)
          else (BigInt(0), BigInt(2).pow(width) - 1)
        if (indexB && minOpt.isEmpty) {
          mat.error(tree.pos, s"Slang @bits ${tree.name.value}'s min should specified when index is enabled.")
          return
        }
        val min = minOpt.getOrElse(wMin)
        val max = maxOpt.getOrElse(wMax)
        val index = if (indexB) min else BigInt(0)
        if (min > max) {
          mat.error(tree.pos, s"Slang @bits ${tree.name.value}'s min ($min) should not be greater than its max ($max).")
          return
        }
        val signedString = if (signed) "signed" else "unsigned"
        if (min < wMin) {
          mat.error(tree.pos, s"Slang @bits ${tree.name.value}'s min ($min) should not be less than its $signedString bit-width minimum ($wMin).")
        }
        if (max > wMax) {
          mat.error(tree.pos, s"Slang @bits ${tree.name.value}'s max ($max) should not be greater than its $signedString bit-width maximum ($wMax).")
        }
        val wrapped = min == wMin && max == wMax
        val cname = tree.name.value
        val typeName = Type.Name(cname)
        val termName = Term.Name(cname)
        val iTermName = zCompanionName(cname)
        val lowerTermName = scPrefix(cname)
        val ctorName = Type.Name(cname)
        val scTypeName = scName(cname)
        val nameStr = Lit.String(cname)
        val isZeroIndex = Lit.Boolean(index == 0)
        val minErrorMessage = Lit.String(s" is less than $cname.Min ($min)")
        val maxErrorMessage = Lit.String(s" is greater than $cname.Max ($max)")

        val (valueTypeName, bvType, boxerType, minLit, maxLit, indexLit, apply, intObject, longObject, bigIntObject) = width match {
          case 8 => (
            scalaByte,
            init"_root_.org.sireum.Z.BV.Byte[$typeName]",
            init"_root_.org.sireum.Z.Boxer.Byte",
            q"(${Lit.Int(min.toInt)}).toByte",
            q"(${Lit.Int(max.toInt)}).toByte",
            q"(${Lit.Int(index.toInt)}).toByte",
            q"""def apply(n: $sireumZ): $typeName = n match {
              case n: _root_.org.sireum.Z.MP.Long =>
                if (!isWrapped) {
                  assert(Min.toMP <= n, n.toString + $minErrorMessage)
                  assert(n <= Max.toMP, n.toString + $maxErrorMessage)
                }
                new $ctorName(n.value.toByte)
              case n: _root_.org.sireum.Z.MP.BigInt =>
                if (!isWrapped) {
                  assert(Min.toMP <= n, n.toString + $minErrorMessage)
                  assert(n <= Max.toMP, n.toString + $maxErrorMessage)
                }
                new $ctorName(n.value.toByte)
              case _ => halt(s"Unsupported $$Name creation from $${n.Name}.")
            }""",
            q"""object Int extends _root_.org.sireum.$$ZCompanionInt[$typeName] {
              def apply(n: $scalaInt): $typeName = if (isWrapped) new $ctorName(n.toByte) else $termName($sireumZQ.MP(n))
              def unapply(n: $typeName): $scalaOption[$scalaInt] = $scalaSomeQ(n.toMP.toInt)
            }""",
            q"""object Long extends org.sireum.$$ZCompanionLong[$typeName] {
              def apply(n: $scalaLong): $typeName = if (isWrapped) new $ctorName(n.toByte) else $termName($sireumZQ.MP(n))
              def unapply(n: $typeName): $scalaOption[$scalaLong] = $scalaSomeQ(n.toMP.toLong)
            }""",
            q"""object BigInt extends org.sireum.$$ZCompanionBigInt[$typeName] {
              def apply(n: $scalaBigInt): $typeName = if (isWrapped) new $ctorName(n.toByte) else $termName($sireumZQ.MP(n))
              def unapply(n: $typeName): $scalaOption[$scalaBigInt] = $scalaSomeQ(n.toBigInt)
            }"""
          )
          case 16 => (
            scalaShort,
            init"_root_.org.sireum.Z.BV.Short[$typeName]",
            init"_root_.org.sireum.Z.Boxer.Short",
            q"(${Lit.Int(min.toInt)}).toShort",
            q"(${Lit.Int(max.toInt)}).toShort",
            q"(${Lit.Int(index.toInt)}).toShort",
            q"""def apply(n: $sireumZ): $typeName = n match {
              case n: _root_.org.sireum.Z.MP.Long =>
                if (!isWrapped) {
                  assert(Min.toMP <= n, n.toString + $minErrorMessage)
                  assert(n <= Max.toMP, n.toString + $maxErrorMessage)
                }
                new $ctorName(n.value.toShort)
              case n: _root_.org.sireum.Z.MP.BigInt =>
                if (!isWrapped) {
                  assert(Min.toMP <= n, n.toString + $minErrorMessage)
                  assert(n <= Max.toMP, n.toString + $maxErrorMessage)
                }
                new $ctorName(n.value.toShort)
              case _ => halt(s"Unsupported $$Name creation from $${n.Name}.")
            }""",
            q"""object Int extends org.sireum.$$ZCompanionInt[$typeName] {
              def apply(n: $scalaInt): $typeName = if (isWrapped) new $ctorName(n.toShort) else $termName($sireumZQ.MP(n))
              def unapply(n: $typeName): $scalaOption[$scalaInt] = $scalaSomeQ(n.toMP.toInt)
            }""",
            q"""object Long extends org.sireum.$$ZCompanionLong[$typeName] {
              def apply(n: $scalaLong): $typeName = if (isWrapped) new $ctorName(n.toShort) else $termName($sireumZQ.MP(n))
              def unapply(n: $typeName): $scalaOption[$scalaLong] = $scalaSomeQ(n.toMP.toLong)
            }""",
            q"""object BigInt extends org.sireum.$$ZCompanionBigInt[$typeName] {
              def apply(n: $scalaBigInt): $typeName = if (isWrapped) new $ctorName(n.toShort) else $termName($sireumZQ.MP(n))
              def unapply(n: $typeName): $scalaOption[$scalaBigInt] = $scalaSomeQ(n.toBigInt)
            }"""
          )
          case 32 => (
            scalaInt,
            init"_root_.org.sireum.Z.BV.Int[$typeName]",
            init"_root_.org.sireum.Z.Boxer.Int",
            Lit.Int(min.toInt),
            Lit.Int(max.toInt),
            Lit.Int(index.toInt),
            q"""def apply(n: $sireumZ): $typeName = n match {
              case n: _root_.org.sireum.Z.MP.Long =>
                if (!isWrapped) {
                  assert(Min.toMP <= n, n.toString + $minErrorMessage)
                  assert(n <= Max.toMP, n.toString + $maxErrorMessage)
                }
                new $ctorName(n.value.toInt)
              case n: _root_.org.sireum.Z.MP.BigInt =>
                if (!isWrapped) {
                  assert(Min.toMP <= n, n.toString + $minErrorMessage)
                  assert(n <= Max.toMP, n.toString + $maxErrorMessage)
                }
                new $ctorName(n.value.toInt)
              case _ => halt(s"Unsupported $$Name creation from $${n.Name}.")
            }""",
            q"""object Int extends _root_.org.sireum.$$ZCompanionInt[$typeName] {
              def apply(n: $scalaInt): $typeName = if (isWrapped) new $ctorName(n) else $termName($sireumZQ.MP(n))
              def unapply(n: $typeName): $scalaOption[$scalaInt] = {
                val v = n.toMP
                if (_root_.scala.Int.MinValue <= v && v <= _root_.scala.Int.MaxValue) $scalaSomeQ(v.toInt)
                else $scalaNoneQ
              }
            }""",
            q"""object Long extends _root_.org.sireum.$$ZCompanionLong[$typeName] {
              def apply(n: $scalaLong): $typeName = if (isWrapped) new $ctorName(n.toInt) else $termName($sireumZQ.MP(n))
              def unapply(n: $typeName): $scalaOption[$scalaLong] = $scalaSomeQ(n.toMP.toLong)
            }""",
            q"""object BigInt extends _root_.org.sireum.$$ZCompanionBigInt[$typeName] {
              def apply(n: $scalaBigInt): $typeName = if (isWrapped) new $ctorName(n.toInt) else $termName($sireumZQ.MP(n))
              def unapply(n: $typeName): $scalaOption[$scalaBigInt] = $scalaSomeQ(n.toBigInt)
            }"""
          )
          case 64 => (
            scalaLong,
            init"_root_.org.sireum.Z.BV.Long[$typeName]",
            init"_root_.org.sireum.Z.Boxer.Long",
            Lit.Long(min.toLong),
            Lit.Long(max.toLong),
            Lit.Long(index.toLong),
            q"""def apply(n: $sireumZ): $typeName = n match {
              case n: _root_.org.sireum.Z.MP.Long =>
                if (!isWrapped) {
                  assert(Min.toMP <= n, n.toString + $minErrorMessage)
                  assert(n <= Max.toMP, n.toString + $maxErrorMessage)
                }
                new $ctorName(n.value)
              case n: _root_.org.sireum.Z.MP.BigInt =>
                if (!isWrapped) {
                  assert(Min.toMP <= n, n.toString + $minErrorMessage)
                  assert(n <= Max.toMP, n.toString + $maxErrorMessage)
                }
                new $ctorName(n.value.toLong)
              case _ => halt(s"Unsupported $$Name creation from $${n.Name}.")
            }""",
            q"""object Int extends org.sireum.$$ZCompanionInt[$typeName] {
              def apply(n: $scalaInt): $typeName = if (isWrapped) new $ctorName(n) else $termName($sireumZQ.MP(n))
              def unapply(n: $typeName): $scalaOption[$scalaInt] = {
                val v = n.toMP
                if (_root_.scala.Int.MinValue <= v && v <= _root_.scala.Int.MaxValue) $scalaSomeQ(v.toInt)
                else $scalaNoneQ
              }
            }""",
            q"""object Long extends _root_.org.sireum.$$ZCompanionLong[$typeName] {
              def apply(n: $scalaLong): $typeName = if (isWrapped) new $ctorName(n) else $termName($sireumZQ.MP(n))
              def unapply(n: $typeName): $scalaOption[$scalaLong] = {
                val v = n.toMP
                if (_root_.scala.Long.MinValue <= v && v <= _root_.scala.Long.MaxValue) $scalaSomeQ(v.toLongOpt.get)
                else $scalaNoneQ
              }
            }""",
            q"""object BigInt extends _root_.org.sireum.$$ZCompanionBigInt[$typeName] {
              def apply(n: $scalaBigInt): $typeName = if (isWrapped) new $ctorName(n.toLong) else $termName($sireumZQ.MP(n))
              def unapply(n: $typeName): $scalaOption[$scalaBigInt] = $scalaSomeQ(n.toBigInt)
            }"""
          )
          case _ => return
        }

        mat.classReplace(name) =
          if (mat.isScript)
            q"""class $typeName(val value: $valueTypeName) extends $bvType {
                  @inline def Name: $javaString = $termName.Name
                  @inline def BitWidth: $scalaInt = $termName.BitWidth
                  @inline def Min: $typeName = $termName.Min
                  @inline def Max: $typeName = $termName.Max
                  @inline def Index: $typeName = $termName.Index
                  @inline def isZeroIndex: $scalaBoolean = $termName.isZeroIndex
                  @inline def isSigned: $scalaBoolean = $termName.isSigned
                  @inline def isWrapped: $scalaBoolean = $termName.isWrapped
                  @inline def ===(that: $typeName): $sireumB = value == that.value
                  @inline def =!=(that: $typeName): $sireumB = value != that.value
                  @inline def toZ: $sireumZ = toBigInt
                  def make(v: $valueTypeName): $typeName = $termName(v)
                  def boxer = $termName.Boxer
                  override def equals(that: $scalaAny): $scalaBoolean =
                    that match {
                      case that: $typeName => value == that.value
                      case _ => false
                    }
                  override def hashCode: $scalaInt = value
                }""".syntax
          else
            q"""final class $typeName(val value: $valueTypeName) extends _root_.scala.AnyVal with $bvType {
                  @inline def Name: $javaString = $termName.Name
                  @inline def BitWidth: $scalaInt = $termName.BitWidth
                  @inline def Min: $typeName = $termName.Min
                  @inline def Max: $typeName = $termName.Max
                  @inline def Index: $typeName = $termName.Index
                  @inline def isZeroIndex: $scalaBoolean = $termName.isZeroIndex
                  @inline def isSigned: $scalaBoolean = $termName.isSigned
                  @inline def isWrapped: $scalaBoolean = $termName.isWrapped
                  @inline def ===(that: $typeName): $sireumB = value == that.value
                  @inline def =!=(that: $typeName): $sireumB = value != that.value
                  @inline def toZ: $sireumZ = toBigInt
                  def make(v: $valueTypeName): $typeName = $termName(v)
                  def boxer = $termName.Boxer
                }""".syntax
        val objectMembers = Seq(
          q"object Boxer extends $boxerType { def make(o: $valueTypeName): $typeName = new $ctorName(o) }",
          q"val Name: $javaString = $nameStr",
          q"val BitWidth: $scalaInt = ${Lit.Int(width)}",
          q"val Min: $typeName = new $ctorName($minLit)",
          q"val Max: $typeName = new $ctorName($maxLit)",
          q"val Index: $typeName = new $ctorName($indexLit)",
          q"val isZeroIndex: $scalaBoolean = $isZeroIndex",
          q"val isSigned: $scalaBoolean = ${Lit.Boolean(signed)}",
          q"val isWrapped: $scalaBoolean = ${Lit.Boolean(wrapped)}",
          q"val isBitVector: $scalaBoolean = true",
          q"val hasMin: $scalaBoolean = true",
          q"val hasMax: $scalaBoolean = true",
          q"def fromZ(n: $sireumZ): $typeName = apply(n)",
          q"def random: $typeName = fromZ($sireumZQ.randomBetween(Min.toZ, Max.toZ))",
          q"def randomBetween(min: $typeName, max: $typeName): $typeName = fromZ($sireumZQ.randomBetween(min.toZ, max.toZ))",
          q"def randomSeed(seed: $sireumZ): $typeName = fromZ($sireumZQ.randomSeedBetween(seed, Min.toZ, Max.toZ))",
          q"def randomSeedBetween(seed: $sireumZ, min: $typeName, max: $typeName): $typeName = fromZ($sireumZQ.randomSeedBetween(seed, min.toZ, max.toZ))",
          q"def apply(n: $scalaInt): $typeName = Int(n)",
          q"def apply(n: $scalaLong): $typeName = Long(n)",
          apply,
          q"def apply(s: $sireumString): $sireumOption[$typeName] = try $sireumSomeQ($termName.$$String(s.value)) catch { case _: _root_.java.lang.Throwable => $sireumNoneQ[$typeName]() }",
          q"def unapply(n: $typeName): $scalaOption[$sireumZ] = $scalaSomeQ(n.toMP)",
          intObject,
          longObject,
          q"""object $$String extends _root_.org.sireum.$$ZCompanionString[$typeName] {
              def apply(s: $javaString): $typeName = BigInt($sireumZQ.$$String(s).toBigInt)
              def unapply(n: $typeName): $scalaOption[$javaString] = $scalaSomeQ(n.toBigInt.toString)
            }""",
          bigIntObject,
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
          q"implicit val $iTermName: org.sireum.$$ZCompanion[$typeName] = this"
        ).map(_.syntax)
        mat.objectMembers.getOrElseUpdate(name, MSeq()) ++= objectMembers
        mat.objectSupers.getOrElseUpdate(name, MSeq()) += t"_root_.org.sireum.$$ZCompanion[$typeName]".syntax
      case _ =>
        mat.error(tree.pos, s"Invalid Slang @bits on: ${tree.syntax}")
    }

  }
}
