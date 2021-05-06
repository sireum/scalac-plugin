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
import org.sireum.scalac.MetaAnnotationTransformer._
import scala.collection.mutable.{ArrayBuffer => MSeq}

class SigTransformer(mat: MetaAnnotationTransformer) {

  def transform(isImmutable: Boolean, name: Vector[String], tree: Tree): Unit = {
    tree match {
      case tree: Defn.Trait =>
        if (tree.templ.early.nonEmpty ||
          tree.templ.self.decltpe.nonEmpty ||
          tree.templ.self.name.value != "") {
          val ann = if (isImmutable) "@sig" else "@msig"
          mat.error(tree.pos, s"Slang $ann traits have to be of the form '$ann trait <id> ... { ... }'.")
          return
        }
        val tname = tree.name
        val tparams = tree.tparams
        val tVars = tparams.map { tp => Type.Name(tp.name.value) }
        val tpe = if (tVars.isEmpty) tname else t"$tname[..$tVars]"
        val (hasHash, hasEqual, hasString) = hasHashEqualString(tpe, tree.templ.stats, s => mat.error(tree.pos, s))
        val equals =
          if (hasEqual) {
            val eCases =
              List(if (tparams.isEmpty) p"case o: $tname => isEqual(o)"
              else p"case (o: $tname[..$tVars] @unchecked) => isEqual(o)",
                p"case _ => return false")
            List(q"protected override def $$hasEquals = true",
              q"override def equals(o: $scalaAny): $scalaBoolean = { o match { ..case $eCases } }")
          } else List()
        val hash = if (hasHash) List(q"override def hashCode: $scalaInt = { hash.hashCode }") else List()
        val toString =
          if (hasString) List(q"override def toString: $javaString = { string.value }")
          else List()
        mat.classMembers.getOrElseUpdate(name, MSeq()) ++= (hash.map(_.syntax) ++ equals.map(_.syntax) ++ toString.map(_.syntax))
        mat.classSupers.getOrElseUpdate(name, MSeq()) += (if (isImmutable) immutable else mutable).syntax
      case _ =>
        val ann = if (isImmutable) "@sig" else "@msig"
        mat.error(tree.pos, s"Slang $ann can only be applied to traits.")
    }
  }
}
