package org.sireum.scalac

import scala.meta._
import scala.meta.dialects.Scala212
import scala.collection.mutable.{Map => MMap, ArrayBuffer => MSeq, Set => MSet}

class MetaAnnotationTransformer(input: String,
                                error: (Int, String) => Unit) {

  val companionSupers: MMap[Vector[String], MSeq[String]] = MMap()
  val companionMembers: MMap[Vector[String], MSeq[String]] = MMap()
  val classSupers: MMap[Vector[String], MSeq[String]] = MMap()
  val classMembers: MMap[Vector[String], MSeq[String]] = MMap()

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
    tree match {
      case mod"@${ann: Mod.Annot}" =>
        ann.parent match {
          case Some(parent) => ann.syntax match {
            case "@bits" =>
            case "@datatype" =>
            case "@enum" => transformEnum(enclosing, parent)
            case "@ext" =>
            case "@memoize" =>
            case "@msig" =>
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
                def ordinal: org.sireum.Z

                def name: org.sireum.String

                final def hash: org.sireum.Z = hashCode

                final def isEqual(other: Value): org.sireum.B = this == other

                final def compare(that: Value): scala.Int = this.ordinal.compareTo(that.ordinal)
              }
           """
          ,
          q"""final def byName(name: org.sireum.String): org.sireum.Option[Value] =
                elements.elements.find(_.name == name) match {
                  case scala.Some(v) => org.sireum.Some(v)
                  case _ => org.sireum.None()
              }
           """,
          q"""final def byOrdinal(n: org.sireum.Z): org.sireum.Option[Value] =
                if (0 <= n && n < elements.size) org.sireum.Some(elements(n)) else org.sireum.None()
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
            q"def ordinal: org.sireum.Z = ${Lit.Int(i)}",
            q"def name: org.sireum.String = ${Lit.String(sym)}"
          )
          decls :+= q"final case object $tname extends Value { ..$ostats }"
          elements :+= tname
          i += 1
        }
        decls ++= Vector[Stat](
          q"val numOfElements: org.sireum.Z = ${Lit.Int(i)}",
          q"val elements: org.sireum.ISZ[Value] = org.sireum.ISZ[Value](..${elements.toList})"
        )
        companionMembers.getOrElseUpdate(name, MSeq()) ++= decls.map(_.syntax)
        companionSupers.getOrElseUpdate(name, MSeq()) += "org.sireum.EnumSig"
      case _ =>
        error(tree.pos, "Slang @enum can only be used on an object.")
    }
  }

  def error(pos: Position, msg: String): Unit = {
    error(pos.start, msg)
  }
}
