package test

import dotty.tools.dotc.core._
import dotty.tools.dotc.core.Contexts._
import dotty.tools.dotc.core.Symbols._
import dotty.tools.dotc.core.Flags._
import dotty.tools.dotc.core.Types._
import dotty.tools.dotc.util.Texts._
import NameOps._
import dotty.tools.dotc.core.Decorators._
import org.junit.Test

class ShowClassTests extends DottyTest {

  private val blackList = List(
    // the following classes cannot be read correctly because they
    // contain illegally pickled @throws annotations
    "scala.actors.remote.Proxy",
    "scala.actors.remote.Serializer",
    "scala.actors.remote.JavaSerializer",
    "scala.build.genprod",
    "scala.tools.nsc.symtab.classfile.AbstractFileReader",
    "scala.remoting.Channel",
    "scala.runtime.remoting.RegistryDelegate",
    "scala.concurrent.Future",
    "scala.concurrent.impl.Future",
    "scala.concurrent.Await",
    "scala.concurrent.Awaitable",
    "scala.concurrent.impl.Promise",
    // the following packages and classes cannot be read because
    // they refer to external libraries which are not available
    // (apache.ant, usually)
    "scala.tools.ant",
    "scala.tools.partest.PartestTask",
    "dotty.tools.dotc.core.pickling.AbstractFileReader")

  def doTwice(test: Context => Unit)(implicit ctx: Context): Unit = {
    test(ctx.fresh.withSetting(ctx.base.settings.debug, true))
    test(ctx.fresh.withSetting(ctx.base.settings.debug, false))
  }

  def showPackage(pkg: TermSymbol)(implicit ctx: Context): Unit = doTwice { implicit ctx =>
    val path = pkg.fullName.toString
    if (blackList contains path)
      println(s"blacklisted package: $path")
    else {
      for (
        sym <- pkg.info.decls if sym.owner == pkg.moduleClass && !(sym.name contains '$')
      ) {
        println(s"showing $sym in ${pkg.fullName}")
        if (sym is Package) showPackage(sym.asTerm)
        else if (sym.isClass) showClass(sym)
        else if (sym is Module) showClass(sym.moduleClass)
      }
    }
  }

  def showPackage(path: String)(implicit ctx: Context): Unit =
    showPackage(ctx.requiredPackage(path))

  def showClass(cls: Symbol)(implicit ctx: Context) = {
    val path = cls.fullName.stripModuleClassSuffix.toString
    if (blackList contains path)
      println(s"blacklisted: $path")
    else {
      println(s"showing $path -> ${cls.denot}")
      val cinfo = cls.info
      val infoText: Text = if (cinfo.exists) cinfo.toText else " is missing"
      println("======================================")
      println((cls.toText ~ infoText).show)
    }
  }

  def showClasses(path: String)(implicit ctx: Context): Unit = doTwice { implicit ctx =>
    println(s"showing file $path")
    val cls = ctx.requiredClass(path.toTypeName)
    showClass(cls)
    showClass(cls.linkedClass)
  }

  @Test
  def loadSimpleClasses() = {
    showClasses("scala.Array")
    showClasses("scala.math.Ordering")
  }

  @Test
  def loadJavaClasses() = {
    showPackage("scala.tools.jline")
  }

  @Test
  def loadMoreClasses() = {
    showClasses("scala.collection.JavaConversions")
    showClasses("scala.collection.convert.Wrappers")
    showClasses("scala.collection.mutable.WeakHashMap")
    showClasses("scala.collection.GenIterable")
    showClasses("scala.collection.Traversable")
    showClasses("scala.collection.LinearSeqLike")
    showClasses("scala.collection.immutable.List")
    showClasses("scala.collection.convert.Wrappers")
    showClasses("scala.collection.generic.package")
    showClasses("scala.collection.MapLike")
    showClasses("scala.Function1")
  }

  @Test
  def loadScalaReflect() = {
    showPackage(ctx.requiredPackage("scala.reflect"))
  }

  @Test
  def loadScalaCollection() = {
    showPackage(ctx.requiredPackage("scala.collection"))
  }

  @Test
  def loadClassWithPrivateInnerAndSubSelf() = {
    showClasses("scala.tools.nsc.settings.ScalaSettings")
    showClasses("scala.tools.jline.console.history.MemoryHistory")
  }

  @Test
  def loadDotty() = {
    showPackage("dotty")
  }

  @Test
  def showReflectAliases() = { // tests for cycles during findMember
    showClasses("scala.reflect.macros.runtime.Aliases")
  }
}
