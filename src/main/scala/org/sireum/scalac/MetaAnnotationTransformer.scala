package org.sireum.scalac

import scala.meta._
import scala.meta.dialects.Scala212
import scala.collection.mutable.{Map => MMap, ArrayBuffer => MSeq, Set => MSet}

class MetaAnnotationTransformer(input: String,
                                var packageName: Vector[String],
                                error: (Int, String) => Unit) {

  val companionSupers: MMap[Vector[String], MSeq[String]] = MMap()
  val companionMembers: MMap[Vector[String], MSeq[String]] = MMap()
  val classSupers: MMap[Vector[String], MSeq[String]] = MMap()
  val classMembers: MMap[Vector[String], MSeq[String]] = MMap()
  val classContructorVals: MMap[Vector[String], MSeq[String]] = MMap()

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
            case "@datatype" => transformDatatype(enclosing, parent)
            case "@enum" => transformEnum(enclosing, parent)
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

  def transformDatatype(name: Vector[String], tree: Tree): Unit = {
    tree match {
      case tree: Defn.Trait => transformDatatypeTrait(name, tree)
      case tree: Defn.Class => transformDatatypeClass(name, tree)
      case _ => error(tree.pos, "Slang @datatype can only be used on a class or a trait.")
    }
  }

  def hasHashEquals(tpe: Type, stats: Seq[Stat]): (Boolean, Boolean) = {
    var hasEquals = false
    var hasHash = false
    for (stat <- stats if !(hasEquals && hasHash)) {
      stat match {
        case q"..$_ def hash: Z = $_" => hasHash = true
        case q"..$_ def isEqual($_ : ${tpeopt: Option[Type]}): B = $_" =>
          tpeopt match {
            case Some(t: Type) if tpe.structure == t.structure => hasEquals = true
            case _ =>
          }
        case _ =>
      }
    }
    (hasHash, hasEquals)
  }

  def transformDatatypeTrait(name: Vector[String], tree: Defn.Trait): Unit = {
    if (tree.templ.early.nonEmpty ||
      tree.templ.self.decltpe.nonEmpty ||
      tree.templ.self.name.value != "") {
      error(tree.pos, "Slang @datatype traits have to be of the form '@datatype trait <id> ... { ... }'.")
      return
    }
    val tname = tree.name
    val tparams = tree.tparams
    val tVars = tparams.map { tp => Type.Name(tp.name.value) }
    val tpe = if (tVars.isEmpty) tname else t"$tname[..$tVars]"
    val (hasHash, hasEqual) = hasHashEquals(tpe, tree.templ.stats)
    val equals =
      if (hasEqual) {
        val eCases =
          List(if (tparams.isEmpty) p"case o: $tname => isEqual(o)"
          else p"case (o: $tname[..$tVars] @unchecked) => isEqual(o)",
            p"case _ => false")
        List(q"override def equals(o: scala.Any): scala.Boolean = { if (this eq o.asInstanceOf[scala.AnyRef]) true else o match { ..case $eCases } }")
      } else List()
    val hash = if (hasHash) List(q"override def hashCode: scala.Int = { hash.hashCode }") else List()
    classMembers.getOrElseUpdate(name, MSeq()) ++= (hash.map(_.syntax) ++ equals.map(_.syntax))
    classSupers.getOrElseUpdate(name, MSeq()) += "org.sireum.DatatypeSig"
  }

  def transformDatatypeClass(name: Vector[String], tree: Defn.Class): Unit = {
    val q"..$_ class $tname[..$tparams] ..$_ (...$paramss) extends $template" = tree
    val tVars = tparams.map { tp => Type.Name(tp.name.value) }
    val tpe = if (tVars.isEmpty) tname else t"$tname[..$tVars]"
    val (hasHash, hasEquals) = hasHashEquals(tpe, tree.templ.stats)
    if (paramss.nonEmpty && paramss.head.nonEmpty) {
      var cparams: Vector[String] = Vector()
      var applyParams: Vector[Term.Param] = Vector()
      var oApplyParams: Vector[Term.Param] = Vector()
      var applyArgs: Vector[Term.Name] = Vector()
      var unapplyTypes: Vector[Type] = Vector()
      var unapplyArgs: Vector[Term.Name] = Vector()
      for (param <- paramss.head) {
        if (param.decltpe.nonEmpty) {
          val tpeopt = param.decltpe
          val varName = Term.Name(param.name.value)
          val hidden = param.mods.exists({
            case mod"@hidden" => true
            case _ => false
          })
          cparams :+= varName.value
          applyParams :+= param"$varName: $tpeopt = this.$varName"
          oApplyParams :+= param"$varName: $tpeopt"
          applyArgs :+= varName
          if (!hidden) {
            val Some(tpe) = tpeopt
            unapplyTypes :+= tpe
            unapplyArgs :+= varName
          }
        } else {
          error(param.pos, "Unsupported Slang @datatype parameter form.")
          return
        }
      };
      {
        val hashCode =
          if (hasHash) q"override lazy val hashCode: scala.Int = hash.hashCode"
          else if (hasEquals) q"override lazy val hashCode: scala.Int = 0"
          else q"override lazy val hashCode: scala.Int = { scala.Seq(this.getClass, ..${unapplyArgs.toList}).hashCode }"
        val equals =
          if (hasEquals) {
            val eCases = Vector(if (tparams.isEmpty) p"case o: $tname => isEqual(o)"
            else p"case (o: $tname[..$tVars] @unchecked) => isEqual(o)", p"case _ => false")
            q"override def equals(o: scala.Any): scala.Boolean = { if (this eq o.asInstanceOf[AnyRef]) true else o match { ..case ${eCases.toList} } }"
          } else {
            val eCaseEqs = unapplyArgs.map(arg => q"$arg == o.$arg")
            val eCaseExp = if (eCaseEqs.isEmpty) q"true" else eCaseEqs.tail.foldLeft(eCaseEqs.head)((t1, t2) => q"$t1 && $t2")
            val eCases =
              Vector(if (tparams.isEmpty) p"case o: $tname => if (this.hashCode != o.hashCode) false else $eCaseExp"
              else p"case (o: $tname[..$tVars] @unchecked) => if (this.hashCode != o.hashCode) false else $eCaseExp",
                p"case _ => false")
            q"override def equals(o: scala.Any): scala.Boolean = { if (this eq o.asInstanceOf[scala.AnyRef]) true else o match { ..case ${eCases.toList} } }"
          }
        val apply = q"def apply(..${applyParams.toList}): $tpe = { new $tname(..${applyArgs.toList}) }"
        val toString = {
          var appends = applyArgs.map(arg => q"sb.append(_root_.org.sireum.String.escape($arg))")
          appends =
            if (appends.isEmpty) appends
            else appends.head +: appends.tail.flatMap(a => Vector(q"""sb.append(", ")""", a))
          Vector(
            q"""override def toString: java.lang.String = {
                    val sb = new java.lang.StringBuilder
                    sb.append(${Lit.String(tname.value)})
                    sb.append('(')
                    ..${appends.toList}
                    sb.append(')')
                    sb.toString
                  }""",
            q"override def string: _root_.org.sireum.String = { toString }"
          )
        }
        val content = {
          var fields = List[Term](q"(${Lit.String("type")}, List[Predef.String](..${(packageName :+ tname.value).map(x => Lit.String(x)).toList}))")
          for (x <- applyArgs) {
            fields ::= q"(${Lit.String(x.value)}, $x)"
          }
          q"override lazy val content: scala.Seq[(Predef.String, scala.Any)] = scala.Seq(..${fields.reverse})"
        }
        classMembers.getOrElseUpdate(name, MSeq()) ++= toString.map(_.syntax) :+ hashCode.syntax :+ equals.syntax :+ apply.syntax :+ content.syntax
        classSupers.getOrElseUpdate(name, MSeq()) += "_root_.org.sireum.DatatypeSig"
        classContructorVals.getOrElseUpdate(name, MSeq()) ++= cparams
      };
      {
        val (apply, unapply) =
          if (tparams.isEmpty)
            (q"def apply(..${oApplyParams.toList}): $tpe = { new $tname(..${applyArgs.toList}) }",
              unapplyTypes.size match {
                case 0 => q"def unapply(o: $tpe): scala.Boolean = { true }"
                case 1 => q"def unapply(o: $tpe): scala.Option[${unapplyTypes.head}] = { scala.Some(o.${unapplyArgs.head}) }"
                case n if n <= 22 => q"def unapply(o: $tpe): scala.Option[(..${unapplyTypes.toList})] = { scala.Some((..${unapplyArgs.map(arg => q"o.$arg").toList})) }"
                case _ =>
                  val unapplyTypess = unapplyTypes.grouped(22).map(types => t"(..${types.toList})").toList
                  val unapplyArgss = unapplyArgs.grouped(22).map(args => q"(..${args.map(a => q"o.$a").toList})").toList
                  q"def unapply(o: $tpe): scala.Option[(..$unapplyTypess)] = { scala.Some((..$unapplyArgss)) }"
              })
          else
            (q"def apply[..$tparams](..${oApplyParams.toList}): $tpe = { new $tname(..${applyArgs.toList}) }",
              unapplyTypes.size match {
                case 0 => q"def unapply[..$tparams](o: $tpe): scala.Boolean = { true }"
                case 1 => q"def unapply[..$tparams](o: $tpe): scala.Option[${unapplyTypes.head}] = { scala.Some(o.${unapplyArgs.head}) }"
                case n if n <= 22 => q"def unapply[..$tparams](o: $tpe): scala.Option[(..${unapplyTypes.toList})] = { scala.Some((..${unapplyArgs.map(arg => q"o.$arg").toList})) }"
                case _ =>
                  val unapplyTypess = unapplyTypes.grouped(22).map(types => t"(..${types.toList})").toList
                  val unapplyArgss = unapplyArgs.grouped(22).map(args => q"(..${args.map(a => q"o.$a").toList})").toList
                  q"def unapply[..$tparams](o: $tpe): scala.Option[(..$unapplyTypess)] = { scala.Some((..$unapplyArgss)) }"
              })
        companionMembers.getOrElseUpdate(name, MSeq()) ++= Vector(apply.syntax, unapply.syntax)
      }
    } else {
      {
        val hashCode =
          if (hasHash) q"override val hashCode: scala.Int = { hash.hashCode }"
          else if (hasEquals) q"override val hashCode: scala.Int = { 0 }"
          else q"override val hashCode: scala.Int = { this.getClass.hashCode }"
        val equals =
          if (hasEquals) {
            val eCases =
              Vector(if (tparams.isEmpty) p"case o: $tname => isEqual(o)"
              else p"case (o: $tname[..$tVars] @unchecked) => isEqual(o)",
                p"case _ => false")
            q"override def equals(o: scala.Any): scala.Boolean = { if (this eq o.asInstanceOf[scala.AnyRef]) true else o match { ..case ${eCases.toList} } }"
          } else {
            val eCases =
              Vector(if (tparams.isEmpty) p"case o: $tname => true"
              else p"case (o: $tname[..$tVars] @unchecked) => true",
                p"case _ => false")
            q"override def equals(o: scala.Any): scala.Boolean = { if (this eq o.asInstanceOf[scala.AnyRef]) true else o match { ..case ${eCases.toList} } }"
          }
        val toString = {
          val r = tname.value + "()"
          Vector(q"""override def toString: java.lang.String = { ${Lit.String(r)} }""", q"override def string: _root_.org.sireum.String = { toString }")
        }
        val content = q"override lazy val content: scala.Seq[(Predef.String, scala.Any)] = scala.Seq((${Lit.String("type")}, List[Predef.String](..${(packageName :+ tname.value).map(x => Lit.String(x)).toList})))"
        classMembers.getOrElseUpdate(name, MSeq()) ++= toString.map(_.syntax) :+ hashCode.syntax :+ equals.syntax :+ content.syntax
        classSupers.getOrElseUpdate(name, MSeq()) += "_root_.org.sireum.DatatypeSig"
      };
      {
        val (v, apply, unapply) =
          if (tparams.isEmpty)
            (q"private[this] val v: scala.AnyRef = { new $tname() }",
              q"def apply(): $tpe = { v.asInstanceOf[$tpe] }",
              q"def unapply(o: $tpe): scala.Boolean = { true }")
          else
            (q"private[this] val v: scala.AnyRef = { new ${t"$tname[..${tparams.map(_ => t"scala.Nothing")}]"}() }",
              q"def apply[..$tparams](): $tpe = { v.asInstanceOf[$tpe] }",
              q"def unapply[..$tparams](o: $tpe): scala.Boolean = { true }")
        companionMembers.getOrElseUpdate(name, MSeq()) ++= Vector(v.syntax, apply.syntax, unapply.syntax)
      }
    }
  }

  def transformEnum(name: Vector[String], tree: Tree): Unit = {
    tree match {
      case tree: Defn.Object =>
        if (tree.templ.early.nonEmpty ||
          tree.templ.inits.nonEmpty ||
          tree.templ.self.decltpe.nonEmpty ||
          tree.templ.self.name.value != "") {
          error(tree.pos, s"Invalid @enum form on an object; it has to be of the form '@enum object ${tree.name.value} { ... }'.")
          return
        }
        var decls = Vector[Stat](
          q"type Type = Value",
          q"""sealed trait Value extends scala.Ordered[Value] {
                def ordinal: _root_.org.sireum.Z

                def name: _root_.org.sireum.String

                final def hash: _root_.org.sireum.Z = hashCode

                final def isEqual(other: Value): _root_.org.sireum.B = this == other

                final def compare(that: Value): scala.Int = this.ordinal.compareTo(that.ordinal)
              }
           """
          ,
          q"""final def byName(name: _root_.org.sireum.String): _root_.org.sireum.Option[Value] =
                elements.elements.find(_.name == name) match {
                  case scala.Some(v) => _root_.org.sireum.Some(v)
                  case _ => _root_.org.sireum.None()
              }
           """,
          q"""final def byOrdinal(n: _root_.org.sireum.Z): _root_.org.sireum.Option[Value] =
                if (0 <= n && n < elements.size) _root_.org.sireum.Some(elements(n)) else _root_.org.sireum.None()
           """
        )
        var elements = Vector[Term.Name]()
        var i = 0
        for (stat <- tree.templ.stats) {
          val sym = stat match {
            case Lit.Symbol(s) => s.name
            case Term.Apply(Term.Select(Term.Name("scala"), Term.Name("Symbol")), Seq(Lit.String(s))) => s
            case _ =>
              error(stat.pos, s"Slang @enum can only have symbols for enum element names: ${stat.syntax}")
              return
          }
          val tname = Term.Name(sym)
          val ostats = List[Stat](
            q"def ordinal: _root_.org.sireum.Z = ${Lit.Int(i)}",
            q"def name: _root_.org.sireum.String = ${Lit.String(sym)}"
          )
          decls :+= q"final case object $tname extends Value { ..$ostats }"
          elements :+= tname
          i += 1
        }
        decls ++= Vector[Stat](
          q"val numOfElements: _root_.org.sireum.Z = ${Lit.Int(i)}",
          q"val elements: _root_.org.sireum.ISZ[Value] = _root_.org.sireum.ISZ[Value](..${elements.toList})"
        )
        companionMembers.getOrElseUpdate(name, MSeq()) ++= decls.map(_.syntax)
        companionSupers.getOrElseUpdate(name, MSeq()) += "_root_.org.sireum.EnumSig"
      case _ =>
        error(tree.pos, "Slang @enum can only be used on an object.")
    }
  }

  def error(pos: Position, msg: String): Unit = {
    error(pos.start, msg)
  }
}
