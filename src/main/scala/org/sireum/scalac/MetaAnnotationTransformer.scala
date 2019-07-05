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
import scala.collection.mutable.{Map => MMap, ArrayBuffer => MSeq, Set => MSet}

object MetaAnnotationTransformer {
  val sireumB = t"_root_.org.sireum.B"
  val sireumZ = t"_root_.org.sireum.Z"
  val sireumString = t"_root_.org.sireum.String"
  val sireumOption = t"_root_.org.sireum.Option"
  val sireumIS = t"_root_.org.sireum.IS"
  val sireumMS = t"_root_.org.sireum.MS"
  val sireumImmutable = t"_root_.org.sireum.Immutable"
  val sireumISZ = t"_root_.org.sireum.ISZ"

  val sireumZQ = q"_root_.org.sireum.Z"
  val sireumSomeQ = q"_root_.org.sireum.Some"
  val sireumNoneQ = q"_root_.org.sireum.None"
  val sireumISQ = q"_root_.org.sireum.IS"
  val sireumMSQ = q"_root_.org.sireum.MS"
  val sireumISZQ = q"_root_.org.sireum.ISZ"

  val javaString = t"_root_.java.lang.String"

  val scalaAny = t"_root_.scala.Any"
  val scalaNothing = t"_root_.scala.Nothing"
  val scalaAnyVal = t"_root_.scala.AnyVal"
  val scalaAnyRef = t"_root_.scala.AnyRef"
  val scalaBoolean = t"_root_.scala.Boolean"
  val scalaByte = t"_root_.scala.Byte"
  val scalaShort = t"_root_.scala.Short"
  val scalaInt = t"_root_.scala.Int"
  val scalaLong = t"_root_.scala.Long"
  val scalaBigInt = t"_root_.scala.BigInt"
  val scalaSeq = t"_root_.scala.Seq"
  val scalaOption = t"_root_.scala.Option"

  val scalaIntQ = q"_root_.scala.Int"
  val scalaLongQ = q"_root_.scala.Long"
  val scalaBigIntQ = q"_root_.scala.BigInt"
  val scalaSomeQ = q"_root_.scala.Some"
  val scalaNoneQ = q"_root_.scala.None"
  val scalaListQ = q"_root_.scala.List"
  val scalaSeqQ = q"_root_.scala.Seq"

  val enumSig = t"_root_.org.sireum.EnumSig"
  val datatypeSig = t"_root_.org.sireum.DatatypeSig"
  val immutable = t"_root_.org.sireum.Immutable"
  val mutable = t"_root_.org.sireum.Mutable"
  val recordSig = t"_root_.org.sireum.RecordSig"

  val sireumStringEscape = q"_root_.org.sireum.String.escape"
  val helperAssign = q"_root_.org.sireum.helper.$$assign"
  val helperCloneAssign = q"_root_.org.sireum.helper.cloneAssign"
  val helperClone = q"_root_.org.sireum.helper.clone"

  def hasHashEqualString(tpe: Type, stats: Seq[Stat], error: String => Unit): (Boolean, Boolean, Boolean) = {
    var hasEqual = false
    var hasHash = false
    var hasString = false
    for (stat <- stats if !(hasEqual && hasHash && hasString)) {
      stat match {
        case stat: Defn.Def =>
          stat.name.value match {
            case "hash" => hasHash = true
            case "isEqual" => hasEqual = true
            case "string" => hasString = true
            case _ =>
          }
        case _ =>
      }
    }
    if (hasHash != hasEqual) {
      if (hasHash) {
        error(s"Method hash is defined, but isEqual is not.")
      }
      else {
        error("Method isEqual is defined, but hash is not.")
      }
    }
    (hasHash, hasEqual, hasString)
  }

  def normNum(s: String): String = {
    val sb = new java.lang.StringBuilder(s.length)
    for (c <- s) c match {
      case ',' | ' ' | '_' =>
      case _ => sb.append(c)
    }
    sb.toString
  }

  def extractInt(tree: Any): Option[BigInt] = tree match {
    case Lit.Int(n) => Some(n)
    case Lit.Long(n) => Some(n)
    case Term.Apply(Term.Name("Z"), Seq(Lit.Int(n))) => Some(n)
    case Term.Apply(Term.Name("Z"), Seq(Lit.Long(n))) => Some(n)
    case Term.Apply(Term.Name("Z"), Seq(Lit.String(n))) => Some(BigInt(normNum(n)))
    case Term.Apply(Term.Select(Term.Apply(Term.Name("StringContext"), Seq(Lit.String(s))), Term.Name("z")), Seq()) =>
      try Some(BigInt(normNum(s))) catch {
        case _: Throwable => None
      }
    case tree: Term.Interpolate if tree.prefix.value == "z" && tree.args.isEmpty && tree.parts.size == 1 =>
      tree.parts.head match {
        case Lit.String(s) => try Some(BigInt(normNum(s))) catch {
          case _: Throwable => None
        }
        case _ => None
      }
    case _ => None
  }

  def extractBoolean(tree: Any): Option[Boolean] = tree match {
    case Lit.Boolean(b) => Some(b)
    case Term.Name("T") => Some(true)
    case Term.Name("F") => Some(false)
    case _ => None
  }

  def zCompanionName(name: String): Pat.Var = Pat.Var(Term.Name(s"$$${name}Companion"))

  def scName(name: String): Type.Name = Type.Name(name + "$Slang")

  def scPrefix(name: String): Term.Name = Term.Name(s"${name.head.toLower}${name.tail}")

}

import MetaAnnotationTransformer._

class MetaAnnotationTransformer(val isScript: Boolean,
                                input: String,
                                var packageName: Vector[String],
                                errorAt: (Int, String) => Unit) {

  val objectSupers: MMap[Vector[String], MSeq[String]] = MMap()
  val objectMembers: MMap[Vector[String], MSeq[String]] = MMap()
  val adtTraits: MSet[Vector[String]] = MSet()
  val classSupers: MMap[Vector[String], MSeq[String]] = MMap()
  val classMembers: MMap[Vector[String], MSeq[String]] = MMap()
  val classReplace: MMap[Vector[String], String] = MMap()
  val objectMemberReplace: MMap[Vector[String], String] = MMap()
  val classMemberReplace: MMap[Vector[String], String] = MMap()
  val bt = new BitsTransformer(this)
  val dt = new DatatypeTransformer(this)
  val et = new EnumTransformer(this)
  val ext = new ExtTransformer(this)
  val mt = new MemoizeTransformer(this)
  val rt = new RangeTransformer(this)
  val rdt = new RecordTransformer(this)
  val st = new SigTransformer(this)

  def transform(): Int = {
    implicit val dialect: scala.meta.Dialect =
      if (isScript) scala.meta.dialects.Scala212.copy(allowToplevelTerms = true)
      else scala.meta.dialects.Scala212
    input.
      replaceAllLiterally("\r\n", "\n"). // HACK: https://github.com/scalameta/scalameta/issues/443
      parse[Source] match {
      case Parsed.Success(tree) =>
        for (stat <- tree.stats) {
          transformTree(Vector(), stat)
        }
        -1
      case Parsed.Error(pos, _, _) => pos.start
    }
  }

  def transformTree(enclosing: Vector[String], tree: Tree): Unit = {
    def name(ref: Term): Vector[String] = ref match {
      case ref: Term.Select => name(ref.qual) :+ ref.name.value
      case ref: Term.Name => Vector(ref.value)
    }

    tree match {
      case mod"@${ann: Mod.Annot}" =>
        ann.parent match {
          case Some(parent) => ann.syntax match {
            case "@datatype" => dt.transform(enclosing, parent)
            case "@enum" => et.transform(enclosing, parent)
            case "@helper" => // skip
            case "@hidden" => // skip
            case "@memoize" => mt.transform(enclosing, parent)
            case "@msig" => st.transform(isImmutable = false, enclosing, parent)
            case "@pure" => // skip
            case "@strictpure" => // skip
            case "@record" => rdt.transform(enclosing, parent)
            case "@sig" => st.transform(isImmutable = true, enclosing, parent)
            case "@spec" => // skip
            case annSyntax =>
              ann.init.tpe.syntax match {
                case "range" if ann.init.argss.size == 1 => rt.transform(enclosing, parent, ann.init.argss.head)
                case "bits" if ann.init.argss.size == 1 => bt.transform(enclosing, parent, ann.init.argss.head)
                case "ext" if ann.init.argss.size == 1 => ext.transform (enclosing, parent, ann.init.argss.head)
                case "ext" if ann.init.argss.isEmpty => ext.transform (enclosing, parent, List())
                case _ => error(tree.pos, s"Invalid annotation $annSyntax.")
              }
          }
          case _ =>
        }
      case _ =>
        val e = tree match {
          case q"package object $ename extends $_" =>
            error(tree.pos, s"Package object is unsupported in Slang.")
            return
          case q"package $eref { ..$_ }" =>
            packageName = name(eref)
            enclosing
          case tree: Defn.Object => enclosing :+ tree.name.value
          case tree: Defn.Class => enclosing :+ tree.name.value
          case tree: Defn.Trait => enclosing :+ tree.name.value
          case _ => enclosing
        }
        for (child <- tree.children) {
          transformTree(e, child)
        }
    }
  }

  def error(pos: Position, msg: String): Unit = {
    errorAt(pos.start, msg)
  }
}
