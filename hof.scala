import sexp._

sealed abstract class Exp
case class Literal(v: Int) extends Exp
case class Let(v : String,
               rhs: Exp,
               body : Exp) extends Exp
case class Ref(v : String) extends Exp
case class Lambda(id: String, body: Exp) extends Exp
case class Call(e1 : Exp, eargs: List[Exp]) extends Exp

def parseExp(e: SExp) : Exp = {
    e match {
      case SInt(v) => Literal(v)
      case SSymbol(id) => Ref(id)
      case SList(SSymbol("let"),
                 SList(SList(SSymbol(id), rhs)),
                 body) =>
        Let(id, parseExp(rhs), parseExp(body))
      case SList(
        SSymbol("lambda"),
        SList(SSymbol(id)),
        body
      ) =>
        Lambda(id, parseExp(body))
      case SCons(e1, e2) =>
        Call(parseExp(e1), e2.asInstanceOf[SCons].toList.map(parseExp _))
      case _ => throw new IllegalArgumentException(
                  "not a valid expression")
    }
}

type Env = Map[String,Val]

abstract class Val
case class VInt(v : Int) extends Val
case class Closure(v : Lambda, e : Env) extends Val
case class Primitive(name : String) extends Val

def interpExp(e: Exp, env : Env) : Val = {
    e match {
        case Literal(v) => VInt(v)
        case Call(e1, eargs) => {
            val v1 = interpExp(e1, env)
            val vargs = eargs.map {
              (e : Exp) => interpExp(e, env)
            }
            v1 match {
              case Closure(Lambda(id, body), env2) => {
                val List(v2) = vargs
                val newEnv = env2 + (id -> v2)
                interpExp(body, newEnv)
              }
              case Primitive("+") =>
                val VInt(arg0) = vargs(0)
                val VInt(arg1) = vargs(1)
                VInt(arg0 + arg1)
              case Primitive("*") =>
                val VInt(arg0) = vargs(0)
                val VInt(arg1) = vargs(1)
                VInt(arg0 * arg1)
              case _ => throw new RuntimeException(
                "tried to call a non-function"
              )
            }
        }
        case Lambda(id, body) => Closure(Lambda(id, body), env)
        case Ref(id) => env.get(id) match {
          case None => throw new RuntimeException("unbound variable")
          case Some(v) => v
        }
        case Let(id, rhs, body) =>
            val rhsVal = interpExp(rhs, env)
            val newEnv = env + (id -> rhsVal)
            interpExp(body, newEnv)
    }
}

val initialEnv : Env = Map(
    "+" -> Primitive("+"),
    "*" -> Primitive("*")
)

def evalExp(e : String) : Val =
  interpExp(parseExp(parseSExp(e)), initialEnv)


println(evalExp("(* (+ 5 2) 1)"))
// Arithmetic tests
assert(evalExp("(* (+ 5 2) 1)") == VInt(7))

// Let tests
assert(evalExp(
  """(let ((x 5))
       (+ x 7))""")
     == VInt(12))

assert(evalExp(
  """(let ((x (+ 5 6)))
       (+ x 7))""")
 == VInt(18))

assert(evalExp(
  """(let ((x (let ((y 1))
                 (+ y 2))))
        (+ x 3))""")
    == VInt(6))

assert(evalExp(
  """
  (let ((double (lambda (n) (* n 2))))
    (double 5))
  """) == VInt(10))

// We'll make this work Wednesday.
assert(evalExp(
  """
  (let ((two 2))
    (let ((double (lambda (n) (* n two))))
      (double 5)))
  """) == VInt(10))


assert(evalExp(
  """
  (((lambda (x) (lambda (y) x))
    5)
   6)
  """)
  == VInt(5))

assert(evalExp(
  """
  (let ((twice (lambda (f) (lambda (arg) (f (f arg))))))
    ((twice (lambda (x) (* x 2))) 5))
  """)
  == VInt(20))


assert(evalExp(
  """
  (let ((apply (lambda (f) (f 3 4))))
    (apply +))
  """
) == VInt(7))

// vim: set ts=2 sw=2 et:
