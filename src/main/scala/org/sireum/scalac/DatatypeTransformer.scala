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
import MetaAnnotationTransformer._
import scala.collection.mutable.{ArrayBuffer => MSeq}

class DatatypeTransformer(mat: MetaAnnotationTransformer) {

  def transform(name: Vector[String], tree: Tree): Unit = {
    tree match {
      case tree: Defn.Trait => transformTrait(name, tree)
      case tree: Defn.Class => transformClass(name, tree)
      case _ => mat.error(tree.pos, "Slang @datatype can only be used on a class or a trait.")
    }
  }

  def transformTrait(name: Vector[String], tree: Defn.Trait): Unit = {
    if (tree.templ.early.nonEmpty ||
      tree.templ.self.decltpe.nonEmpty ||
      tree.templ.self.name.value != "") {
      mat.error(tree.pos, "Slang @datatype traits have to be of the form '@datatype trait <id> ... { ... }'.")
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
            p"case _ => halt(${Lit.String("Invalid equality test between ")} + this.getClass + ${Lit.String(" and ")} + o.getClass)")
        List(q"final protected override val $$hasEquals = true",
          q"override def equals(o: $scalaAny): $scalaBoolean = { o match { ..case $eCases } }")
      } else List()
    val hash = if (hasHash) List(q"override def hashCode: $scalaInt = { hash.hashCode }") else List()
    val toString =
      if (hasString) List(q"override def toString: $javaString = { string.value }")
      else List()
    mat.classMembers.getOrElseUpdate(name, MSeq()) ++= (hash.map(_.syntax) ++ equals.map(_.syntax) ++ toString.map(_.syntax))
    mat.classSupers.getOrElseUpdate(name, MSeq()) += datatypeSig.syntax
  }

  def transformClass(name: Vector[String], tree: Defn.Class): Unit = {
    if (tree.templ.early.nonEmpty ||
      tree.templ.self.decltpe.nonEmpty ||
      tree.templ.self.name.value != "") {
      mat.error(tree.pos, "Slang @datatype classes have to be of the form '@record class <id> ... (...) ... { ... }'.")
      return
    }
    val q"..$_ class $tname[..$tparams] ..$_ (...$paramss) extends $_" = tree
    val tVars = tparams.map { tp => Type.Name(tp.name.value) }
    val tpe = if (tVars.isEmpty) tname else t"$tname[..$tVars]"
    val (hasHash, hasEqual, hasString) = hasHashEqualString(tpe, tree.templ.stats, s => mat.error(tree.pos, s))
    if (paramss.nonEmpty && paramss.head.nonEmpty) {
      var vars: Vector[Stat] = Vector()
      var applyParams: Vector[Term.Param] = Vector()
      var oApplyParams: Vector[Term.Param] = Vector()
      var applyArgs: Vector[Term.Name] = Vector()
      var unapplyTypes: Vector[Type] = Vector()
      var unapplyArgs: Vector[Term.Name] = Vector()
      for (param <- paramss.head) {
        if (param.decltpe.nonEmpty) {
          val tpeopt = param.decltpe
          val paramName = Term.Name(param.name.value)
          val hidden = param.mods.exists({
            case mod"@hidden" => true
            case _ => false
          })
          val varName = Term.Name("_" + paramName.value)
          vars :+= q"def $paramName = $varName"
          val getterName = Term.Name(s"get${paramName.value.head.toUpper}${paramName.value.substring(1)}")
          vars :+= q"def $getterName = $varName"
          applyParams :+= param"$paramName: $tpeopt = this.$paramName"
          oApplyParams :+= param"$paramName: $tpeopt"
          applyArgs :+= paramName
          if (!hidden) {
            unapplyTypes :+= tpeopt.get
            unapplyArgs :+= paramName
          }
        } else {
          mat.error(param.pos, "Unsupported Slang @datatype parameter form.")
          return
        }
      }

      {
        val hashCode =
          if (hasHash) q"override lazy val hashCode: $scalaInt = hash.hashCode"
          else if (hasEqual) q"override lazy val hashCode: $scalaInt = 0"
          else q"override lazy val hashCode: $scalaInt = { $scalaSeqQ(this.getClass, ..${unapplyArgs.toList}).hashCode }"
        val equals =
          if (hasEqual) {
            val eCases = Vector(if (tparams.isEmpty) p"case o: $tname => isEqual(o)"
            else p"case (o: $tname[..$tVars] @unchecked) => isEqual(o)",
              p"case _ => halt(${Lit.String("Invalid equality test between ")} + this.getClass + ${Lit.String(" and ")} + o.getClass)")
            q"override def equals(o: $scalaAny): $scalaBoolean = { if (this eq o.asInstanceOf[$scalaAnyRef]) true else o match { ..case ${eCases.toList} } }"
          } else {
            val eCaseEqs = unapplyArgs.map(arg => q"this.$arg == o.$arg")
            val eCaseExp = if (eCaseEqs.isEmpty) q"true" else eCaseEqs.tail.foldLeft(eCaseEqs.head)((t1, t2) => q"$t1 && $t2")
            val eCases =
              Vector(if (tparams.isEmpty) p"case o: $tname => if (this.hashCode != o.hashCode) false else $eCaseExp"
              else p"case (o: $tname[..$tVars] @unchecked) => if (this.hashCode != o.hashCode) false else $eCaseExp",
                p"case _ => false")
            q"override def equals(o: $scalaAny): $scalaBoolean = { if ($$hasEquals) super.equals(o) else if (this eq o.asInstanceOf[$scalaAnyRef]) true else o match { ..case ${eCases.toList} } }"
          }
        val apply = q"def apply(..${applyParams.toList}): $tpe = { new $tname(..${applyArgs.toList}) }"
        val toString = {
          if (hasString) Vector(q"override def toString: $javaString = { string.value }")
          else {
            var appends = applyArgs.map(arg => q"sb.append($sireumStringEscape(this.$arg))")
            appends =
              if (appends.isEmpty) appends
              else appends.head +: appends.tail.flatMap(a => Vector(q"""sb.append(", ")""", a))
            Vector(q"""override def toString: $javaString = {
                            val sb = new _root_.java.lang.StringBuilder
                            sb.append(${Lit.String(tname.value)})
                            sb.append('(')
                            ..${appends.toList}
                            sb.append(')')
                            sb.toString
                          }""",
              q"override def string: $sireumString = { toString }")
          }
        }
        val content = {
          var fields = List[Term](q"(${Lit.String("type")}, $scalaListQ[$javaString](..${(mat.packageName :+ tname.value).map(x => Lit.String(x)).toList}))")
          for (x <- applyArgs) {
            fields ::= q"(${Lit.String(x.value)}, this.$x)"
          }
          q"override lazy val $$content: $scalaSeq[($javaString, $scalaAny)] = $scalaSeqQ(..${fields.reverse})"
        }
        mat.classMembers.getOrElseUpdate(name, MSeq()) ++= vars.map(_.syntax) ++ toString.map(_.syntax) :+ hashCode.syntax :+ equals.syntax :+ apply.syntax :+ content.syntax
        mat.classSupers.getOrElseUpdate(name, MSeq()) += datatypeSig.syntax
      }

      {
        val (apply, unapply) =
          if (tparams.isEmpty)
            (q"def apply(..${oApplyParams.toList}): $tpe = { new $tname(..${applyArgs.toList}) }",
              unapplyTypes.size match {
                case 0 => q"def unapply(o: $tpe): $scalaBoolean = { true }"
                case 1 => q"def unapply(o: $tpe): $scalaOption[${unapplyTypes.head}] = { $scalaSomeQ(o.${unapplyArgs.head}) }"
                case n if n <= 22 => q"def unapply(o: $tpe): $scalaOption[(..${unapplyTypes.toList})] = { $scalaSomeQ((..${unapplyArgs.map(arg => q"o.$arg").toList})) }"
                case _ =>
                  val unapplyTypess = unapplyTypes.grouped(22).map(types => t"(..${types.toList})").toList
                  val unapplyArgss = unapplyArgs.grouped(22).map(args => q"(..${args.map(a => q"o.$a").toList})").toList
                  q"def unapply(o: $tpe): $scalaOption[(..$unapplyTypess)] = { $scalaSomeQ((..$unapplyArgss)) }"
              })
          else
            (q"def apply[..$tparams](..${oApplyParams.toList}): $tpe = { new $tname(..${applyArgs.toList}) }",
              unapplyTypes.size match {
                case 0 => q"def unapply[..$tparams](o: $tpe): $scalaBoolean = { true }"
                case 1 => q"def unapply[..$tparams](o: $tpe): $scalaOption[${unapplyTypes.head}] = { $scalaSomeQ(o.${unapplyArgs.head}) }"
                case n if n <= 22 => q"def unapply[..$tparams](o: $tpe): $scalaOption[(..${unapplyTypes.toList})] = { $scalaSomeQ((..${unapplyArgs.map(arg => q"o.$arg").toList})) }"
                case _ =>
                  val unapplyTypess = unapplyTypes.grouped(22).map(types => t"(..${types.toList})").toList
                  val unapplyArgss = unapplyArgs.grouped(22).map(args => q"(..${args.map(a => q"o.$a").toList})").toList
                  q"def unapply[..$tparams](o: $tpe): $scalaOption[(..$unapplyTypess)] = { $scalaSomeQ((..$unapplyArgss)) }"
              })
        mat.objectMembers.getOrElseUpdate(name, MSeq()) ++= Vector(apply.syntax, unapply.syntax)
      }
    } else {
      {
        val hashCode =
          if (hasHash) q"override val hashCode: $scalaInt = { hash.hashCode }"
          else if (hasEqual) q"override val hashCode: $scalaInt = { 0 }"
          else q"override val hashCode: $scalaInt = { this.getClass.hashCode }"
        val equals =
          if (hasEqual) {
            val eCases =
              Vector(if (tparams.isEmpty) p"case o: $tname => isEqual(o)"
              else p"case (o: $tname[..$tVars] @unchecked) => isEqual(o)",
                p"case _ => halt(${Lit.String("Invalid equality test between ")} + this.getClass + ${Lit.String(" and ")} + o.getClass)")
            q"override def equals(o: $scalaAny): $scalaBoolean = { if (this eq o.asInstanceOf[$scalaAnyRef]) true else o match { ..case ${eCases.toList} } }"
          } else {
            val eCases =
              Vector(if (tparams.isEmpty) p"case o: $tname => true"
              else p"case (o: $tname[..$tVars] @unchecked) => true",
                p"case _ => false")
            q"override def equals(o: $scalaAny): $scalaBoolean = { if ($$hasEquals) super.equals(o) else if (this eq o.asInstanceOf[$scalaAnyRef]) true else o match { ..case ${eCases.toList} } }"
          }
        val toString = {
          if (hasString) Vector(q"override def toString: $javaString = { string.value }")
          else Vector(q"""override def toString: $javaString = { ${Lit.String(tname.value + "()")} }""",
            q"override def string: $sireumString = { toString }")
        }
        val content = q"override lazy val $$content: $scalaSeq[($javaString, $scalaAny)] = $scalaSeqQ((${Lit.String("type")}, $scalaListQ[$javaString](..${(mat.packageName :+ tname.value).map(x => Lit.String(x)).toList})))"
        mat.classMembers.getOrElseUpdate(name, MSeq()) ++= toString.map(_.syntax) :+ hashCode.syntax :+ equals.syntax :+ content.syntax
        mat.classSupers.getOrElseUpdate(name, MSeq()) += datatypeSig.syntax
      }

      {
        val (v, apply, unapply) =
          if (tparams.isEmpty)
            (q"private[this] val $$v: $scalaAnyRef = { new $tname() }",
              q"def apply(): $tpe = { $$v.asInstanceOf[$tpe] }",
              q"def unapply(o: $tpe): $scalaBoolean = { true }")
          else
            (q"private[this] val $$v: $scalaAnyRef = { new ${t"$tname[..${tparams.map(_ => scalaNothing)}]"}() }",
              q"def apply[..$tparams](): $tpe = { $$v.asInstanceOf[$tpe] }",
              q"def unapply[..$tparams](o: $tpe): $scalaBoolean = { true }")
        mat.objectMembers.getOrElseUpdate(name, MSeq()) ++= Vector(v.syntax, apply.syntax, unapply.syntax)
      }
    }
  }
}
