import sexp._

sealed abstract class Exp
case class Literal(v: SExp) extends Exp
case class Add(lhs: Exp, rhs: Exp) extends Exp
case class Subtract(lhs: Exp, rhs: Exp) extends Exp
case class Multiply(lhs: Exp, rhs: Exp) extends Exp
case class Call(lhs : String, rhs : Exp) extends Exp
case class Let(v : String,
               rhs: Exp,
               body : Exp) extends Exp
case class Ref(v : String) extends Exp
case class Conditional(cond: Exp, true_case: Exp, false_case: Exp) extends Exp
case class Equal(lhs: Exp, rhs: Exp) extends Exp
case class Null() extends Exp
case class Quote(exp: SExp) extends Exp
case class Cons(lhs: Exp, rhs: Exp) extends Exp
case class Cars(lhs: Exp, rhs: Exp) extends Exp
case class Cdr(lhs: Exp, rhs: Exp) extends Exp
case class NullFunc(e: Exp) extends Exp

case class Pair(head: Exp, tail: Exp) extends Exp


case class Def(name : String, arguments : List[String], body : Exp)
case class Program(defs : List[Def], exp : Exp)



def parseProgram(p: SExp) : Program = parseProgramHelper(p, Nil)

def parseProgramHelper(p : SExp, acc : List[Def]) : Program = {
  p match {
      case SNil => throw new IllegalArgumentException("Invalid program")
      case SCons(first, rest) =>{
        first match {
          // TODO: Change how we parse the program, to allow for multiple arguments
          // Try matching the first part of each list, and seeing if defines or a function name is called
          case SList(SSymbol(name), SInt(value)) =>
            Program(acc.reverse, parseExp(first))
          case _ => parseProgramHelper(rest,  parseFunction(first) :: acc)
        }
      }
  }
}

def parseArgs(args : SList, acc : List[String]) : List[String] = {
  args match {
    case SNil => acc
    case SCons(first, rest) =>
      first :: parseArgs(args, acc)
  }
}

def parseFunction(function: SExp) : Def  = {
  function match {
    case SList(SSymbol("define"), list, body) =>
      list match {
        case SCons(name, rest) =>
          Def(name, parseArgs(rest, Nil), parseExp(body))
      }
      case _ => throw new IllegalArgumentException("Invalid function definitons")
  }
}

def parseExp(e: SExp) : Exp = {
    e match {
      case STrue() => Literal(STrue())
      case SFalse() => Literal(SFalse())
      case SInt(v) => Literal(SInt(v))
      case SList(SSymbol("+"), l, r) =>
        Add(parseExp(l), parseExp(r))
      case SList(SSymbol("-"), l, r) =>
        Subtract(parseExp(l), parseExp(r))
      case SList(SSymbol("*"), l, r) =>
        Multiply(parseExp(l), parseExp(r))
      case SSymbol(id) => Ref(id)
      case SList(SSymbol("let"),
                 SList(SList(SSymbol(id), rhs)),
                 body) =>
        Let(id, parseExp(rhs), parseExp(body))
      // TODO: Implement handling functions of multiple parameters, need to parse an SList
      case SList(SSymbol(id), e) => Call(id, parseExp(e))
      case SList(SSymbol("if"), cond, t, f) =>
        Conditional(parseExp(cond), parseExp(t), parseExp(f))
      case SList(SSymbol("equal?"), lhs, rhs) =>
        Equal(parseExp(lhs), parseExp(rhs))
      case _ => throw new IllegalArgumentException(
                  "not a valid expression")
    }
}

type Env = Map[String, SExp]

def findFunction(l: List[Def], name: String) : Def = {
  l match {
    case Nil => throw new RuntimeException("Function not defined")
    case head :: tail => {
      if(head.name == name)
        head
      else
        findFunction(tail, name)
    }
  }
}

def interpExp(e: Exp, env : Env, functions : List[Def]) : SExp = {
    e match {
        case Literal(v) => v
        case Call(f, e) => {
          val func = findFunction(functions, f)
          interpExp(func.body, env + (func.argument -> interpExp(e, env, functions)),
            functions)
        }
        case Add(l,r) => {
          val lv = interpExp(l, env, functions)
          val rv = interpExp(r, env, functions)
          (lv, rv) match {
            case (SInt(l), SInt(r)) => SInt(l + r)
            case _ => throw new RuntimeException("An error occurred while adding")
          }
        }
        case Subtract(l,r) => {
          val lv = interpExp(l, env, functions)
          val rv = interpExp(r, env, functions)

          (lv, rv) match {
            case (SInt(l), SInt(r)) => SInt(l-r)
            case _ => throw new RuntimeException("An error occurred while subtracting")
          }
        }
        case Multiply(l,r) => {
          val lv = interpExp(l, env, functions)
          val rv = interpExp(r, env, functions)
          (lv, rv) match {
            case (SInt(l), SInt(r)) => SInt(l * r)
            case _ => throw new RuntimeException("An error occurred while multipling")
          }
        }
        case Ref(id) => env.get(id) match {
          case None => throw new RuntimeException("unbound variable")
          case Some(v) => v
        }
        case Let(id, rhs, body) =>{
            val rhsVal = interpExp(rhs, env, functions)
            val newEnv = env + (id -> rhsVal)
            interpExp(body, newEnv, functions)
        }
        case Conditional(cond, t, f) => {
          val condition = interpExp(cond, env, functions)
          condition match {
                case SInt(a) =>
                  if (a > 0)
                    interpExp(t, env, functions)
                  else
                    interpExp(f, env, functions)
                case STrue() => interpExp(t, env, functions)
                case SFalse() => interpExp(f, env, functions)
                case _ => throw new RuntimeException("unable to parse conditional")
            }
        }
      case Equal(l,r) => {
        val lv = interpExp(l, env, functions)
        val rv = interpExp(r, env, functions)

        (lv, rv) match {
          case (SInt(l), SInt(v)) =>
            if(l == v)
              STrue()
            else
              SFalse()
          case (STrue(), STrue()) => STrue()
          case (SFalse(), SFalse()) => STrue()
          case _ => SFalse()
        }
      }
    }
}

def interpProgram(p : Program) : SExp = interpExp(p.exp, Map(), p.defs)
def evalExp(e : String) : SExp = interpExp(parseExp(parseSExp(e)), Map(), List())

def evalProgram(p : String) : SExp  =
  interpProgram(parseProgram(parseSExp(p)))


// Arithmetic tests
val arithEx1 = parseExp(parseSExp("(* (- 5 2) 1)"))

// Let tests
val letEx1 = parseExp(parseSExp(
  """(let ((x 5))
       (+ x 7))"""))
assert(interpExp(letEx1, Map(), List()) == SInt(12))

val letEx2 = parseExp(parseSExp(
  """(let ((x (+ 5 6)))
       (+ x 7))"""))
assert(interpExp(letEx2, Map(), List()) == SInt(18))

val letEx3 = parseExp(parseSExp(
  """(let ((x (let ((y 1))
                 (+ y 2))))
        (+ x 3))"""))
assert(interpExp(letEx3, Map(), List()) == SInt(6))

// Program parsing tests. We'll represent a program
// as a sequence of defintions, followed by a main
val progEx1 = parseProgram(parseSExp(
"""
((define (square n)
   (* n n))
 (square 5))
"""))
(progEx1 ==
  Program(List(
    Def("square", "n", Multiply(Ref("n"), Ref("n")))
  ),
  Call("square", Literal(SInt(5))))
)
