package org.sireum.scalac

import scala.meta._

object ExtTransformer {

  val extSuffix = "_Ext"
  val dollar: String = Term.Name("$").structure

}

import ExtTransformer._

class ExtTransformer(mat: MetaAnnotationTransformer) {
  def transform(name: Vector[String], tree: Tree, args: List[Term]): Unit = {
    tree match {
      case tree: Defn.Object =>
        if (tree.templ.early.nonEmpty ||
          tree.templ.self.decltpe.nonEmpty ||
          tree.templ.self.name.value != "") {
          mat.error(tree.pos, s"Invalid @ext object form; it has to be of the form '@ext object ${tree.name.value} { ... }'.")
          return
        }
        var extObjName = tree.name.value + extSuffix
        if (args.size == 1) {
          args.head match {
            case q"name = ${exp: Lit.String}" => extObjName = exp.value
            case q"${exp: Lit.String}" => extObjName = exp.value
            case _ =>
              mat.error(args.head.pos, s"""Invalid @ext name argument; it has to be of the form 'name = "..."' or '"..."'.""")
              return
          }
        }
        val extName = Term.Name(extObjName)
        for (stat <- tree.templ.stats) stat match {
          case q"..$mods val ${x: Pat.Var}: $tpeopt = $$" =>
            if (mods.nonEmpty || tpeopt.isEmpty) {
              mat.error(stat.pos, s"Invalid Slang @ext on a val; it has to be of the form: 'val <id>: <type> = $$'")
              return
            }
            val varName = x.name
            val valDef = stat.asInstanceOf[Defn.Val]
            mat.objectMemberReplace(name :+ varName.value) = valDef.copy(rhs = q"$extName.$varName").syntax
          case q"..$mods var ${x: Pat.Var}: $tpeopt = $$" =>
            if (mods.nonEmpty || tpeopt.isEmpty) {
              mat.error(stat.pos, s"Invalid Slang @ext on a var; it has to be of the form: 'var <id>: <type> = $$'")
              return
            }
            val varName = x.name
            val varDef = stat.asInstanceOf[Defn.Var]
            mat.objectMemberReplace(name :+ varName.value) = varDef.copy(rhs = Some(q"$extName.$varName")).syntax
          case stat: Defn.Def if stat.mods.exists { case mod"@spec" => true; case _ => false } =>
            // skip
          case stat: Defn.Def =>
            if (stat.paramss.size > 1) {
              mat.error(stat.pos, s"Slang @ext object methods should only have a list of parameters (instead of several lists of parameters).")
              return
            }
            if (stat.decltpe.isEmpty) {
              mat.error(stat.pos, s"Slang @ext object methods should be explicitly typed.")
              return
            }
            val tVars = stat.tparams.map { tp => Type.Name(tp.name.value) }
            val params = if (stat.paramss.isEmpty) List() else stat.paramss.head.map { p => Term.Name(p.name.value) }
            if (stat.body.structure == dollar) {
            } else stat.body match {
              case Term.Apply(Term.Select(Term.Apply(Term.Name("StringContext"), _), Term.Name("l")), _) =>
              case expr: Term.Interpolate if expr.prefix.value == "l" =>
              case _ =>
                mat.error(stat.pos, "Invalid expression for Slang @ext object method; it should be either $ or l\"\"\"{ ... }\"\"\".")
                return
            }
            val mname = stat.name
            val newStat = if (tVars.isEmpty)
              if (stat.paramss.isEmpty) stat.copy(body = q"$extName.$mname")
              else stat.copy(body = q"$extName.$mname(..$params)")
            else
              if (stat.paramss.isEmpty) stat.copy(body = q"$extName.$mname[..$tVars]")
              else stat.copy(body = q"$extName.$mname[..$tVars](..$params)")
            mat.objectMemberReplace(name :+ mname.value) = newStat.syntax
          case tree: Defn.Trait =>
            if (tree.tparams.nonEmpty ||
              tree.templ.early.nonEmpty ||
              tree.templ.inits.nonEmpty ||
              tree.templ.self.decltpe.nonEmpty ||
              tree.templ.self.name.value != "") {
              mat.error(stat.pos, s"Invalid trait inside Slang @ext object; it has to be of the form: 'trait ${tree.name.value}'")
            }
            mat.objectMemberReplace(name :+ tree.name.value) = q"type ${tree.name} = $extName.${tree.name}".syntax
          case Term.Apply(Term.Select(Term.Apply(Term.Name("StringContext"), _), Term.Name("l")), _) =>
            // skip
          case expr: Term.Interpolate if expr.prefix.value == "l" =>
            // skip
          case stat: Defn.Val =>
            // skip
          case stat: Defn.Var if stat.rhs.nonEmpty =>
            // skip
          case _ =>
            mat.error(stat.pos, s"Invalid Slang @ext object member: ${stat.syntax}.")
            return
        }

      case _ => mat.error(tree.pos, s"Slang @ext can only be used on an object.")
    }

  }
}
