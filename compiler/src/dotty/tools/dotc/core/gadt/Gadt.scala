package dotty.tools
package dotc
package core
package gadt

import Decorators._
import Symbols._
import Types._
import Flags._
import Contexts._
import Variances._
import dotty.tools.dotc.reporting.trace
import config.Printers._
import util.Property._

object Gadt:
  val KnowledgeKey: Key[Knowledge] = new Key[Knowledge]


  def apply(tc: TypeComparer, pat: Type, scrut: Type)(using ctx: Context): Boolean = {
    val k = new Knowledge
    ctx.moreProperties = ctx.moreProperties + (KnowledgeKey -> k)
    pat match {
      case AppliedType(tycon, param) =>
        println("Tycon: " + tycon)
        println("Params: " + param)
//        HKTypeLambda(
//          List(_$1),
//          List(TypeBounds(Nothing,
//               HKTypeLambda(List(_$2),
//                            List(TypeBounds(Nothing, Any)), Any))), AppliedType(TypeRef(NoPrefix,type f),List(TypeParamRef(_$1))))

//        HKTypeLambda(
//          List(_$1),
//          List(TypeBounds(TypeRef(ThisType(TypeRef(NoPrefix,module class scala)),class Nothing),
//            TypeRef(ThisType(TypeRef(NoPrefix,module class scala)),class Any))), AppliedType(TypeRef(NoPrefix,type f),
//            List(TypeParamRef(_$1))))
        println("Eta exp (tree): " + param.head.EtaExpand(param.head.typeParams))
        println(i"Eta exp: ${param.head.EtaExpand(param.head.typeParams)}")
        param.head match {
          case f: TypeRef =>
            println("GOT A TYPEREF "+f)
            println("OF SIMPLE KIND ? "+f.hasSimpleKind)
            println("SYMBOL "+f.symbol)
            println("INFO (tree) "+f.info)
            println(i"INFO ${f.info}")
            println(i"TYPARAM ${f.typeParams}")
            val bounds = f.typeParams.map(_.paramInfo)
            val gotBounds = HKTypeLambda.boundsFromParams(f.typeParams, TypeBounds.empty)
            val got = typer.ProtoTypes.newTypeVar(gotBounds)
            println("THE BOUNDS: "+bounds)
            println("GOTBOUNDS tree: "+gotBounds)
            println(i"GOTBOUNDS: $gotBounds")
            println(s"GOT: $got")
            println(s"GOT TYPARAM: ${got.typeParams.map(_.paramInfo)}")
            println("SAME KIND ?: "+got.hasSameKindAs(f))
          case _ => println("Not a typeref")
        }

//        val freshTvar = typer.ProtoTypes.newTypeVar(TypeBounds.upper(HKTypeLambda.any(1)))
//        println("FRESH TVAR:")
//        println("Tree: "+freshTvar)
//        println(i"Pretty-print $freshTvar")
//        println("Of simple kind? "+freshTvar.hasSimpleKind)
//        println("Same kind as f? "+freshTvar.hasSameKindAs(f))
//        println("HKResult "+freshTvar.hkResult)
//        println(s"Eta exp: ${freshTvar.EtaExpand(freshTvar.typeParams)}")

    }
//    k.TFindOrCreateEC(pat, Nil, true, true)
    /*
     List(LambdaParam(
        HKTypeLambda(List(_$1),
          List(TypeBounds(TypeRef(ThisType(TypeRef(NoPrefix,module class scala)),class Nothing),TypeRef(ThisType(TypeRef(NoPrefix,module class scala)),class Any))),
          TypeRef(ThisType(TypeRef(NoPrefix,module class scala)),class Any),
          List()),
        0))
    */

    true
  }
