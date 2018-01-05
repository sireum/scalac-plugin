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

import scala.meta._
import scala.meta.dialects.Scala212
import scala.collection.mutable.{Map => MMap, ArrayBuffer => MSeq, Set => MSet}

object MetaAnnotationTransformer {
  val sireumB = t"_root_.sireum.B"
  val sireumZ = t"_root_.sireum.Z"
  val sireumString = t"_root_.sireum.String"
  val sireumOption = t"_root_.sireum.Option"
  val sireumISZ = t"_root_.sireum.ISZ"

  val sireumSomeQ = q"_root_.sireum.Some"
  val sireumNoneQ = q"_root_.sireum.None"
  val sireumISZQ = q"_root_.sireum.ISZ"

  val scalaAny = t"_root_.scala.Any"
  val scalaNothing = t"_root_.scala.Nothing"
  val scalaAnyRef = t"_root_.scala.AnyRef"
  val scalaBoolean = t"_root_.scala.Boolean"
  val scalaInt = t"_root_.scala.Int"
  val javaString = t"_root_.java.lang.String"
  val scalaSeq = t"_root_.scala.Seq"
  val scalaOption = t"_root_.scala.Option"

  val scalaSomeQ = q"_root_.scala.Some"
  val scalaListQ = q"_root_.scala.List"
  val scalaSeqQ = q"_root_.scala.Seq"

  val enumSig = t"_root_.org.sireum.EnumSig"
  val datatypeSig = t"_root_.org.sireum.DatatypeSig"

  val sireumStringEscape = q"_root_.org.sireum.String.escape"

  def hasHashEqualString(tpe: Type, stats: Seq[Stat]): (Boolean, Boolean, Boolean) = {
    var hasEqual = false
    var hasHash = false
    var hasString = false
    for (stat <- stats if !(hasEqual && hasHash)) {
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
    (hasHash, hasEqual, hasString)
  }
}

import MetaAnnotationTransformer._

class MetaAnnotationTransformer(input: String,
                                var packageName: Vector[String],
                                errorAt: (Int, String) => Unit) {

  val companionSupers: MMap[Vector[String], MSeq[String]] = MMap()
  val companionMembers: MMap[Vector[String], MSeq[String]] = MMap()
  val classSupers: MMap[Vector[String], MSeq[String]] = MMap()
  val classMembers: MMap[Vector[String], MSeq[String]] = MMap()
  val classContructorVals: MMap[Vector[String], MSeq[String]] = MMap()
  val dt = new DatatypeTransformer(this)
  val et = new EnumTransformer(this)

  def transform(): Int = {
    input.parse[Source] match {
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
            case "@bits" =>
            case "@datatype" => dt.transform(enclosing, parent)
            case "@enum" => et.transform(enclosing, parent)
            case "@ext" =>
            case "@hidden" =>
            case "@memoize" =>
            case "@msig" =>
            case "@pure" =>
            case "@range" =>
            case "@record" =>
            case "@rich" =>
            case "@sig" =>
            case "@spec" => // skip
            case annSyntax => error(tree.pos, s"Unsupported annotation $annSyntax.")
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
