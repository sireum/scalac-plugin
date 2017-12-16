val scalaVer = "2.12.4"

val pluginVersion = "3.1.3-SNAPSHOT"

lazy val sireumScalacPlugin = Project(
  id = "sireum-scalac-plugin",
  base = file(".")).
  settings(Seq(
    organization := "org.sireum",
    name := "scalac-plugin",
    retrieveManaged := true,
    version := pluginVersion,
    scalaVersion := scalaVer,
    scalacOptions := Seq("-target:jvm-1.8", "-deprecation",
    "-Ydelambdafy:method", "-feature", "-unchecked", "-Xfatal-warnings"),
    parallelExecution in Test := true,
    libraryDependencies ++= Seq(
      "org.scala-lang" % "scala-compiler" % scalaVer),
    publishMavenStyle := true,
    publishTo := {
      val nexus = "https://oss.sonatype.org/"
      if (isSnapshot.value)
        Some("snapshots" at nexus + "content/repositories/snapshots")
      else
        Some("releases" at nexus + "service/local/staging/deploy/maven2")
    },
    publishArtifact in Test := false,
    pomIncludeRepository := { _ => false },
    pomExtra :=
      <url>https://github.com/sireum/v3-scalac-plugin/</url>
        <licenses>
          <license>
            <name>Simplified BSD License</name>
            <url>https://github.com/sireum/v3-scalac-plugin/blob/master/license.md</url>
          </license>
        </licenses>
        <scm>
          <url>https://github.com/sireum/v3-scalac-plugin.git</url>
          <connection>scm:git:https://github.com/sireum/v3-scalac-plugin.git</connection>
        </scm>
        <developers>
          <developer>
            <id>robby-phd</id>
            <name>Robby</name>
            <url>http://cs.ksu.edu/~robby</url>
          </developer>
        </developers>
  ))
