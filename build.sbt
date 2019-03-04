val scalaVer = "2.12.8"

val pluginVersion = "4-SNAPSHOT"

val metaVersion = "4.1.4"

addCommandAlias("publish-local", "; project scalac-plugin; publishLocal")
addCommandAlias("publish-signed", "; project scalac-plugin; publishSigned")
addCommandAlias("release", "; project scalac-plugin; sonatypeRelease")


lazy val `scalac-plugin-assembly` = (project in file(".")).settings(Seq(
  organization := "org.sireum",
  name := "scalac-plugin-assembly",
  scalaVersion := scalaVer,
  version := pluginVersion,
  scalacOptions := Seq("-target:jvm-1.8", "-deprecation",
    "-Ydelambdafy:method", "-feature", "-unchecked", "-Xfatal-warnings"),
  assembly / assemblyOption := (assemblyOption in assembly).value.copy(includeScala = false),
  Compile / assembly / artifact := {
    val art = (Compile / assembly / artifact).value
    art.withClassifier(Some("all"))
  },
  assemblyShadeRules in assembly := Seq(
    ShadeRule.rename("com.**" -> "sh4d3.com.@1").inAll,
    ShadeRule.rename("org.langmeta.**" -> "sh4d3.org.langmeta.@1").inAll,
    ShadeRule.rename("org.scalameta.**" -> "sh4d3.org.scalameta.@1").inAll,
    ShadeRule.rename("scala.meta.**" -> "sh4d3.scala.meta.@1").inAll,
    ShadeRule.rename("sourcecode.**" -> "sh4d3.sourcecode.@1").inAll
  ),
  assemblyExcludedJars in assembly := {
    val cp = (fullClasspath in assembly).value
    cp filter {x =>
      x.data.getName.contains("scalapb") ||
        x.data.getName.contains("protobuf") ||
        x.data.getName.contains("fansi") ||
        x.data.getName.contains("lenses") ||
        x.data.getName.contains("pprint")}
  },
  libraryDependencies ++= Seq(
    "org.scala-lang" % "scala-compiler" % scalaVer,
    "org.scalameta" %% "scalameta" % metaVersion
  ),
  skip in publish := true
)).settings(addArtifact(artifact in(Compile, assembly), assembly).settings: _*)

lazy val `scalac-plugin` = project.settings(
  organization := "org.sireum",
  name := "scalac-plugin",
  version := pluginVersion,
  Compile / packageBin  := (assembly in(`scalac-plugin-assembly`, Compile)).value,
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
  pomExtra :=
    <url>https://github.com/sireum/v3-scalac-plugin/</url>
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

