val scalaVer = "2.13.16"

val pluginVersion = "4-SNAPSHOT"

val metaVersion = "4.13.1"

addCommandAlias("publish-local", "; project scalac-plugin; publishLocal")
addCommandAlias("publish-signed", "; project scalac-plugin; publishSigned")
addCommandAlias("release", "; project scalac-plugin; sonatypeRelease")


lazy val `scalac-plugin-assembly` = (project in file(".")).settings(Seq(
  organization := "org.sireum",
  name := "scalac-plugin-assembly",
  scalaVersion := scalaVer,
  version := pluginVersion,
  scalacOptions := Seq("-release", "8", "-deprecation",
    "-Ydelambdafy:method", "-feature", "-unchecked", "-Xfatal-warnings"),
  assembly / assemblyOption ~= { _.withIncludeScala(false) },
  Compile / assembly / artifact := {
    val art = (Compile / assembly / artifact).value
    art.withClassifier(Some("all"))
  },
  assembly / assemblyShadeRules := Seq(
    ShadeRule.rename("com.**" -> "sh4d3.com.@1").inAll,
    ShadeRule.rename("org.langmeta.**" -> "sh4d3.org.langmeta.@1").inAll,
    ShadeRule.rename("org.scalameta.**" -> "sh4d3.org.scalameta.@1").inAll,
    ShadeRule.rename("scala.meta.**" -> "sh4d3.scala.meta.@1").inAll,
    ShadeRule.rename("fastparse.**" -> "sh4d3.fastparse.@1").inAll,
    ShadeRule.rename("sourcecode.**" -> "sh4d3.sourcecode.@1").inAll,
    ShadeRule.rename("geny.**" -> "sh4d3.geny.@1").inAll,
    ShadeRule.rename("org.jline.**" -> "sh4d3.org.jline.@1").inAll,
    ShadeRule.rename("scala.collection.compat.immutable.*" -> "sh4d3.scala.collection.compat.immutable.@1").inAll,
    ShadeRule.rename("scala.collection.compat.immutable.*" -> "sh4d3.scala.collection.compat.immutable.@1").inAll,
    ShadeRule.rename("scala.collection.compat.*" -> "sh4d3.scala.collection.compat.@1").inAll,
    ShadeRule.rename("scala.util.control.compat.*" -> "sh4d3.scala.util.control.compat.@1").inAll,
  ),
  assembly / assemblyExcludedJars := {
    val cp = (assembly / fullClasspath).value
    cp filter {x =>
      x.data.getName.contains("scalapb") ||
        x.data.getName.contains("protobuf") ||
        x.data.getName.contains("fansi") ||
        x.data.getName.contains("lenses") ||
        x.data.getName.contains("pprint") ||
        x.data.getName.contains("scalap")}
  },
  libraryDependencies ++= Seq(
    "org.scala-lang" % "scala-compiler" % scalaVer,
    "org.scalameta" %% "scalameta" % metaVersion
  ),
  publish / skip := true
)).settings(addArtifact(Compile / assembly / artifact, assembly).settings: _*)

lazy val `scalac-plugin` = project.settings(
  organization := "org.sireum",
  name := "scalac-plugin",
  scalaVersion := scalaVer,
  version := pluginVersion,
  Compile / packageBin := (`scalac-plugin-assembly` / Compile / assembly).value,
  publishMavenStyle := true,
  publishTo := {
    val nexus = "https://oss.sonatype.org/"
    if (isSnapshot.value)
      Some("snapshots" at nexus + "content/repositories/snapshots")
    else
      Some("releases" at nexus + "service/local/staging/deploy/maven2")
  },
  Test / publishArtifact := false,
  pomIncludeRepository := { _ => false },
  libraryDependencies := Seq(),
  pomExtra :=
    <url>https://github.com/sireum/scalac-plugin/</url>
      <licenses>
        <license>
          <name>Simplified BSD License</name>
          <url>https://github.com/sireum/scalac-plugin/blob/master/license.md</url>
        </license>
      </licenses>
      <scm>
        <url>https://github.com/sireum/scalac-plugin.git</url>
        <connection>scm:git:https://github.com/sireum/scalac-plugin.git</connection>
      </scm>
      <developers>
        <developer>
          <id>robby-phd</id>
          <name>Robby</name>
          <url>http://cs.ksu.edu/~robby</url>
        </developer>
      </developers>
)

