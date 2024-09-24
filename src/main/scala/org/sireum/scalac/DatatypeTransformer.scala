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
    if (tree.templ.earlyClause.nonEmpty ||
      tree.templ.body.selfOpt.exists(_.decltpe.nonEmpty) ||
      tree.templ.body.selfOpt.exists(_.name.value != "")) {
      mat.error(tree.pos, "Slang @datatype traits have to be of the form '@datatype trait <id> ... { ... }'.")
      return
    }
    val tname = tree.name
    val tparams = tree.tparamClause.values
    val tVars = tparams.map { tp => Type.Name(tp.name.value) }
    val tpe = if (tVars.isEmpty) tname else t"$tname[..$tVars]"
    val (hasHash, hasEqual, hasString) = hasHashEqualString(tpe, tree.templ.body.stats, s => mat.error(tree.pos, s))
    val equals =
      if (hasEqual) {
        val eCases =
          List(if (tparams.isEmpty) p"case o: $tname => isEqual(o)"
          else p"case (o: $tname[..$tVars] @unchecked) => isEqual(o)",
            p"case _ => return false")
        List(q"final protected override val $$hasEquals = true",
          q"override def equals(o: $scalaAny): $scalaBoolean = { o match { ..case $eCases } }")
      } else List()
    val hash = if (hasHash) List(q"override def hashCode: $scalaInt = { hash.hashCode }") else List()
    val toString =
      if (hasString) List(q"final protected override val $$hasString = true",
        q"override def toString: $javaString = { string.value }")
      else List()
    mat.adtTraits.add(name)
    mat.classMembers.getOrElseUpdate(name, MSeq()) ++= (hash.map(_.syntax) ++ equals.map(_.syntax) ++ toString.map(_.syntax))
    mat.classSupers.getOrElseUpdate(name, MSeq()) += datatypeSig.syntax
  }

  def transformClass(name: Vector[String], tree: Defn.Class): Unit = {
    if (tree.templ.earlyClause.nonEmpty ||
      tree.templ.body.selfOpt.exists(_.decltpe.nonEmpty) ||
      tree.templ.body.selfOpt.exists(_.name.value != "")) {
      mat.error(tree.pos, "Slang @datatype classes have to be of the form '@record class <id> ... (...) ... { ... }'.")
      return
    }
    val (tname, tparams, paramss) = (tree.name, tree.tparamClause.values, tree.ctor.paramClauses.map(_.values))
    val tVars = tparams.map { tp => Type.Name(tp.name.value) }
    val tpe = if (tVars.isEmpty) tname else t"$tname[..$tVars]"
    val (hasHash, hasEqual, hasString) = hasHashEqualString(tpe, tree.templ.body.stats, s => mat.error(tree.pos, s))
    var varNames: Vector[Term.Name] = Vector()
    for (stat <- tree.templ.body.stats) {
      stat match {
        case stat: Defn.Val if !stat.mods.exists({
          case mod"@spec" => true
          case _ => false
        }) =>
          for (Pat.Var(name) <- stat.pats) {
            varNames = varNames :+ name
          }
        case _ =>
      }
    }
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
          val paramVarName = Term.Name("__" + paramName.value)
          varNames = varNames :+ paramName
          val getterName = Term.Name(s"get${paramName.value.head.toUpper}${paramName.value.substring(1)}")
          val varName = Term.Name("_" + paramName.value)
          tpeopt match {
            case Some(tpe@t"Option[$t]") =>
              val bvarName = Term.Name("_b" + paramName.value)
              val pvarName = Pat.Var(varName)
              val pbvarName = Pat.Var(bvarName)
              vars :+= q"private[this] val $pbvarName: _root_.scala.Boolean = $paramVarName.isEmpty.value"
              vars :+= q"private[this] val $pvarName: $t = $paramVarName.getOrElse(null.asInstanceOf[$t])"
              vars :+= q"def $paramName: $tpe = if ($bvarName) None() else Some($varName)"
              vars :+= q"def $getterName: $tpe = $paramName"
            case Some(tpe@t"MOption[$t]") =>
              val bvarName = Term.Name("_b" + paramName.value)
              val pbvarName = Pat.Var(bvarName)
              val pvarName = Pat.Var(varName)
              vars :+= q"private[this] val $pbvarName: _root_.scala.Boolean = $paramVarName.isEmpty.value"
              vars :+= q"private[this] val $pvarName: $t = $paramVarName.getOrElse(null.asInstanceOf[$t])"
              vars :+= q"def $paramName: $tpe = if ($bvarName) MNone() else MSome($varName)"
              vars :+= q"def $getterName: $tpe = $paramName"
            case Some(tpe@t"Either[$l, $r]") =>
              val bvarName = Term.Name("_b" + paramName.value)
              val pvarName = Pat.Var(varName)
              val pbvarName = Pat.Var(bvarName)
              vars :+= q"private[this] val $pbvarName: _root_.scala.Boolean = $paramVarName.isRight.value"
              vars :+= q"private[this] val $pvarName: _root_.scala.Any = if ($bvarName) $paramVarName.right else $paramVarName.left"
              vars :+= q"def $paramName: $tpe = if ($bvarName) Either.Right($varName.asInstanceOf[$r]) else Either.Left($varName.asInstanceOf[$l])"
              vars :+= q"def $getterName: $tpe = $paramName"
            case Some(tpe@t"MEither[$l, $r]") =>
              val bvarName = Term.Name("_b" + paramName.value)
              val pvarName = Pat.Var(varName)
              val pbvarName = Pat.Var(bvarName)
              vars :+= q"private[this] val $pbvarName: _root_.scala.Boolean = $paramVarName.isRight.value"
              vars :+= q"private[this] val $pvarName: _root_.scala.Any = if ($bvarName) $paramVarName.right else $paramVarName.left"
              vars :+= q"def $paramName: $tpe = if ($bvarName) MEither.Right($varName.asInstanceOf[$r]) else MEither.Left($varName.asInstanceOf[$l])"
              vars :+= q"def $getterName: $tpe = $paramName"
            case _ =>
              val pvarName = Pat.Var(varName)
              vars :+= q"private[this] val $pvarName = $paramVarName"
              vars :+= q"def $paramName = $varName"
              vars :+= q"def $getterName = $varName"
          }
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
          else q"override lazy val hashCode: $scalaInt = { if ($$hasEquals) super.hashCode else $scalaSeqQ(this.getClass.getName, ..${unapplyArgs.toList}).hashCode }"
        val equals =
          if (hasEqual) {
            val eCases = Vector(if (tparams.isEmpty) p"case o: $tname => isEqual(o)"
            else p"case (o: $tname[..$tVars] @unchecked) => isEqual(o)",
              p"case _ => return false")
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
        val apply = q"def apply(..${applyParams.toList}): $tpe = { new ${init"$tname(..${applyArgs.toList})"} }"
        val toString = {
          if (hasString) Vector(q"override def toString: $javaString = { string.value }")
          else {
            var appends = applyArgs.map(arg => q"sb.append($sireumStringEscape(this.$arg))")
            appends =
              if (appends.isEmpty) appends
              else appends.head +: appends.tail.flatMap(a => Vector(q"""sb.append(", ")""", a))
            Vector(q"""override def toString: $javaString = {
                         if ($$hasString) super.string.value else {
                           val sb = new _root_.java.lang.StringBuilder
                           sb.append(${Lit.String(tname.value)})
                           sb.append('(')
                           ..${appends.toList}
                           sb.append(')')
                           sb.toString
                         }
                       }""",
              q"override def string: $sireumString = { if ($$hasString) super.string else toString }")
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
            (q"def apply(..${oApplyParams.toList}): $tpe = { new ${init"$tname(..${applyArgs.toList})"} }",
              unapplyTypes.size match {
                case 0 => q"def unapply(o: $tpe): true = { true }"
                case 1 => q"def unapply(o: $tpe): $scalaSome[${unapplyTypes.head}] = { $scalaSomeQ(o.${unapplyArgs.head}) }"
                case n if n <= 22 => q"def unapply(o: $tpe): $scalaSome[(..${unapplyTypes.toList})] = { $scalaSomeQ((..${unapplyArgs.map(arg => q"o.$arg").toList})) }"
                case _ =>
                  val unapplyTypess = unapplyTypes.grouped(22).map(types => if (types.size == 1) types.head else t"(..${types.toList})").toList
                  val unapplyArgss = unapplyArgs.grouped(22).map(args =>
                    if (args.size == 1) q"o.${args.head}"
                    else q"(..${args.map(a => q"o.$a").toList})").toList
                  q"def unapply(o: $tpe): $scalaSome[(..$unapplyTypess)] = { $scalaSomeQ((..$unapplyArgss)) }"
              })
          else
            (q"def apply[..$tparams](..${oApplyParams.toList}): $tpe = { new ${init"$tname(..${applyArgs.toList})"} }",
              unapplyTypes.size match {
                case 0 => q"def unapply[..$tparams](o: $tpe): true = { true }"
                case 1 => q"def unapply[..$tparams](o: $tpe): $scalaSome[${unapplyTypes.head}] = { $scalaSomeQ(o.${unapplyArgs.head}) }"
                case n if n <= 22 => q"def unapply[..$tparams](o: $tpe): $scalaSome[(..${unapplyTypes.toList})] = { $scalaSomeQ((..${unapplyArgs.map(arg => q"o.$arg").toList})) }"
                case _ =>
                  val unapplyTypess = unapplyTypes.grouped(22).map(types => if (types.size == 1) types.head else t"(..${types.toList})").toList
                  val unapplyArgss = unapplyArgs.grouped(22).map(args =>
                    if (args.size == 1) q"o.${args.head}"
                    else q"(..${args.map(a => q"o.$a").toList})").toList
                  q"def unapply[..$tparams](o: $tpe): $scalaSome[(..$unapplyTypess)] = { $scalaSomeQ((..$unapplyArgss)) }"
              })
        mat.objectMembers.getOrElseUpdate(name, MSeq()) ++= Vector(apply.syntax, unapply.syntax)
      }
    } else {
      {
        val hashCode =
          if (hasHash) q"override val hashCode: $scalaInt = { hash.hashCode }"
          else if (hasEqual) q"override val hashCode: $scalaInt = { 0 }"
          else q"override val hashCode: $scalaInt = { if ($$hasEquals) super.hashCode else this.getClass.getName.hashCode }"
        val equals =
          if (hasEqual) {
            val eCases =
              Vector(if (tparams.isEmpty) p"case o: $tname => isEqual(o)"
              else p"case (o: $tname[..$tVars] @unchecked) => isEqual(o)",
                p"case _ => return false")
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
          else Vector(q"""override def toString: $javaString = { if ($$hasString) super.string.value else ${Lit.String(tname.value + "()")} }""",
            q"override def string: $sireumString = { if ($$hasString) super.string else toString }")
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
              q"def unapply(o: $tpe): true = { true }")
          else
            (q"private[this] val $$v: $scalaAnyRef = { new ${t"$tname[..${tparams.map(_ => scalaNothing)}]"}() }",
              q"def apply[..$tparams](): $tpe = { $$v.asInstanceOf[$tpe] }",
              q"def unapply[..$tparams](o: $tpe): true = { true }")
        mat.objectMembers.getOrElseUpdate(name, MSeq()) ++= Vector(v.syntax, apply.syntax, unapply.syntax)
      }
    }

    {
      var equivStats = Vector[Term]()
      for (varName <- varNames) {
        equivStats = equivStats :+ q"if (this.$varName =!= o.$varName) return false"
      }
      equivStats = equivStats :+ q"return true"
      val equivCases = Vector(
        if (tparams.isEmpty) p"case o: $tname => { ..${equivStats.toList} }"
        else p"case (o: $tname[..$tVars] @unchecked) => { ..${equivStats.toList} }",
        p"case _ => return false")
      val equiv =
        q"""override def ===(o: $sig): $sireumB = {
              if (this eq o) return true
              o match {
                ..case ${equivCases.toList}
              }
            }"""
      mat.classMembers.getOrElseUpdate(name, MSeq()) ++= Vector(equiv.syntax)
    }

    mat.adtClasses.add(name)
  }
}
