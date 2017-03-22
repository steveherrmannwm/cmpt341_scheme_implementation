import sexp._

sealed abstract class Exp
case class Literal(v: SExp) extends Exp
case class Add(lhs: Exp, rhs: Exp) extends Exp
case class Subtract(lhs: Exp, rhs: Exp) extends Exp
case class Multiply(lhs: Exp, rhs: Exp) extends Exp
case class Call(funcName : String, args : List[Exp]) extends Exp
case class Let(v : String,
               rhs: Exp,
               body : Exp) extends Exp
case class Ref(v : String) extends Exp
case class Conditional(cond: Exp, true_case: Exp, false_case: Exp) extends Exp

case class Equal(lhs: Exp, rhs: Exp) extends Exp
case class LessThan(lhs: Exp, rhs: Exp) extends Exp
case class LessThanEqual(lhs: Exp, rhs: Exp) extends Exp
case class GreaterThan(lhs: Exp, rhs: Exp) extends Exp
case class GreaterThanEqual(lhs: Exp, rhs: Exp) extends Exp

case class Cons(head: Exp, tail: Exp) extends Exp
case class Null(exp: Exp) extends Exp
case class Car(exp: Exp) extends Exp
case class Cdr(exp: Exp) extends Exp
case class Pair(exp: Exp) extends Exp

case class Def(name : String, arguments : List[String], body : Exp)
case class Program(defs : List[Def], exp : Exp)


def parseProgram(p: SExp) : Program = parseProgramHelper(p, Nil)

def parseProgramHelper(p : SExp, acc : List[Def]) : Program = {
  p match {
      case SNil => throw new IllegalArgumentException("Invalid program")
      case SCons(first, rest) =>{
        first match {
          // Try matching the first part of each list, and seeing if defines or a function name is called
        case SNil => throw new IllegalArgumentException("Invalid program")
        case SCons(definition, remaining) => {
          definition match {
            case SSymbol("define") =>
              parseProgramHelper(rest, parseFunction(first) :: acc)
            case _  => {
              Program(acc.reverse, parseExp(first))
            }
          }
        }
      }
    }
  }
}

def parseArgs(args : SExp, acc : List[String]) : List[String] = {
  args match {
    case SNil => acc
    case SCons(SSymbol(first), rest) =>{
      first :: parseArgs(rest, acc)
    }
  }
}

def parseFunction(function: SExp) : Def  = {
  function match {
    case SList(SSymbol("define"), list, body) =>
      list match {
        case SCons(SSymbol(name), rest) =>
          Def(name, parseArgs(rest, Nil), parseExp(body))
      }
      case _ => throw new IllegalArgumentException("Invalid function definitons")
  }
}

def parseExp(e: SExp) : Exp = {
    e match {
      case SNil => Literal(SNil)
      case STrue() => Literal(STrue())
      case SFalse() => Literal(SFalse())
      case SInt(v) => Literal(SInt(v))
      case SList(SSymbol("quote"), exp) => Literal(exp)
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
      case SList(SSymbol("lambda"), SList(args), body) =>
        Lambda(args, parseExp(body))
      case SList(SSymbol("if"), cond, t, f) =>
        Conditional(parseExp(cond), parseExp(t), parseExp(f))
      case SList(SSymbol("equal?"), lhs, rhs) =>
        Equal(parseExp(lhs), parseExp(rhs))
      case SList(SSymbol("<"), lhs, rhs) =>
        LessThan(parseExp(lhs), parseExp(rhs))
      case SList(SSymbol("<="), lhs, rhs) =>
        LessThanEqual(parseExp(lhs), parseExp(rhs))
      case SList(SSymbol(">"), lhs, rhs) =>
        GreaterThan(parseExp(lhs), parseExp(rhs))
      case SList(SSymbol(">="), lhs, rhs) =>
        GreaterThanEqual(parseExp(lhs), parseExp(rhs))
      case SList(SSymbol("cons"), h, t) =>
        Cons(parseExp(h), parseExp(t))
      case SList(SSymbol("car"), exp) =>
        Car(parseExp(exp))
      case SList(SSymbol("cdr"), exp) =>
        Cdr(parseExp(exp))
      case SList(SSymbol("pair?"), exp) =>
        Pair(parseExp(exp))
      case SList(SSymbol("null?"), exp) =>
        Null(parseExp(exp))
      // If we're dealing with a function, we may not know how many arguments we're dealing with, so use a special function
      case function => function match {
        case SNil => throw new IllegalArgumentException("Illegal function call")
        case SCons(SSymbol(id), args) => {
          parseFunctionCall(id, args, Nil)
        }
      }
    }
}

def parseFunctionCall(name: String, function: SExp, acc: List[Exp]) : Exp = {
  function match {
    case SNil => Call(name, acc.reverse)
    case SCons(first, rest) =>
      parseFunctionCall(name, rest, parseExp(first) ::acc)
  }
}

type Env = Map[String, SExp]
case class Closure(lambda: Exp, env: Env) extends SExp
case class Primitive(name: String) extends SExp

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

def interpFuncArgs(argNames : List[String], argVals : List[Exp], acc: Env, env: Env, functions : List[Def]) : Map[String, SExp] = {
  (argNames, argVals) match {
    case (Nil, Nil) => {
      acc
    }
    case (argName :: args, argVal :: vals) => {
      interpFuncArgs(args, vals, acc + (argName -> interpExp(argVal, env, functions)), env, functions)
    }
   case (Nil, head :: tail) => throw new RuntimeException("Too many arguments were called for the function")
    case (head:: tail, Nil) => throw new RuntimeException("Function missing required arguments")
  }
}

def interpExp(e: Exp, env : Env, functions : List[Def]) : SExp = {
    e match {
        case Literal(v) => v
        case Call(f, e) => {
          val func = findFunction(functions, f)
          // Provide scoping and sets the argument values for our functions
          val ma = interpFuncArgs(func.arguments, e, Map(), env, functions)
          interpExp(func.body, ma, functions)
        }
        case Lambda(args, body) => {
          
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
        case Ref(id) =>
          env.get(id) match {
          case None => throw new RuntimeException("unbound variable")
          case Some(v) => {
            v
          }
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
          lv == rv
        }
      }
      case GreaterThan(l, r) => {
        val lv = interpExp(l, env, functions)
        val rv = interpExp(r, env, functions)
        (lv, rv) match {
          case (SInt(l), SInt(v)) => {
            if(l > v)
              STrue()
            else
              SFalse()
          }
          case (STrue(), SFalse()) => STrue()
          case (STrue(), STrue()) => SFalse()
          case (SFalse(), STrue()) => SFalse()
          case (SFalse(), SFalse()) => SFalse()
          case _ => throw new RuntimeException("Tried to compare two types of SExps")
        }
      }
      case GreaterThanEqual(l, r) => {
        val lv = interpExp(l, env, functions)
        val rv = interpExp(r, env, functions)
        (lv, rv) match {
          case (SInt(l), SInt(v)) => {
            if(l >= v)
              STrue()
            else
              SFalse()
          }
          case (STrue(), SFalse()) => STrue()
          case (STrue(), STrue()) => STrue()
          case (SFalse(), STrue()) => SFalse()
          case (SFalse(), SFalse()) => STrue()
          case _ => throw new RuntimeException("Tried to compare two types of SExps")
        }
      }
      case LessThan(l, r) => {
        val lv = interpExp(l, env, functions)
        val rv = interpExp(l, env, functions)
        (lv, rv) match {
          case (SInt(l), SInt(v)) => {
            if(l < v)
              STrue()
            else
              SFalse()
          }
          case (STrue(), SFalse()) => SFalse()
          case (STrue(), STrue()) => SFalse()
          case (SFalse(), STrue()) => STrue()
          case (SFalse(), SFalse()) => SFalse()
          case _ => throw new RuntimeException("Tried to compare two types of SExps")
        }
      }
      case LessThanEqual(l, r) => {
        val lv = interpExp(l, env, functions)
        val rv = interpExp(l, env, functions)
        (lv, rv) match {
          case (SInt(l), SInt(v)) => {
            if(l < v)
              STrue()
            else
              SFalse()
          }
          case (STrue(), SFalse()) => SFalse()
          case (STrue(), STrue()) => STrue()
          case (SFalse(), STrue()) => STrue()
          case (SFalse(), SFalse()) => STrue()
          case _ => throw new RuntimeException("Tried to compare two types of SExps")
        }
      }
      case Cons(l, r) => {
        SCons(interpExp(l, env, functions), interpExp(r, env, functions))
      }
      case Car(exp) =>
      {
        val l = interpExp(exp, env, functions)
        l match {
          case SNil => throw new RuntimeException("Structure given to car wasn't a pair")
          case SCons(head, tail) => {
            head
          }
        }
      }
      case Cdr(exp) => {
        val l = interpExp(exp, env, functions)
        l match {
          case SNil => throw new RuntimeException("structure given to Cdr wasn't a pair")
          case SCons(head, tail) => tail
        }
      }
      case Pair(exp) => {
        val l = interpExp(exp, env, functions)

        l match {
          case SList(a) => STrue()
          case _ => SFalse()
        }
      }
      case Null(exp) => {
        val l = interpExp(exp, env , functions)
        l match {
          case SNil => STrue()
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
    Def("square", List("n"), Multiply(Ref("n"), Ref("n")))
  ),
  Call("square", List(Literal(SInt(5)))))
)

val progEx3 = parseProgram(parseSExp("""
 ((define (append l s)
      (if (null? l)
             s
                  (cons (car l) (append (cdr l) s))))
               (append (quote (1 2 3)) (quote (4 5 6))))
  """))
// Returns the sum of the power sums of a given x and n from n to 0
// Only works with positive integers for x and n
// x must also be at least 1
val testProg = parseProgram(parseSExp("""
 ((define (pow x exp)
   (if (equal? exp 0)
     1
     (* x (pow x (- exp 1)))
     ))
  (define (sumOfPows a exp) (if (equal? a 0)
    0
    (+ (pow a exp) (sumOfPows (- a 1) exp))))
  (define (sumsOfPows a exp) (if (equal? exp 1)
    (sumOfPows a 1)
    (+ (sumOfPows a exp) (sumsOfPows a (- exp 1)))))
  (sumsOfPows 3 3)
  )
  """))
assert(interpProgram(testProg) == SInt(56))
val testProg2 = parseProgram(parseSExp("""
 ((define (pow x exp)
   (if (equal? exp 0)
     1
     (* x (pow x (- exp 1)))
     ))
  (define (sumOfPows a exp) (if (equal? a 1)
    1
    (+ (pow a exp) (sumOfPows (- a 1) exp))))
  (define (sumsOfPows a exp) (if (equal? exp 1)
    (sumOfPows a 1)
    (+ (sumOfPows a exp) (sumsOfPows a (- exp 1)))))
  (sumsOfPows 5 4)
  )
  """))
assert(interpProgram(testProg2) == SInt(1274))
val testProg3 = parseProgram(parseSExp("""
 ((define (pow x exp)
   (if (equal? exp 0)
     1
     (* x (pow x (- exp 1)))
     ))
  (define (sumOfPows a exp) (if (equal? a 1)
    1
    (+ (pow a exp) (sumOfPows (- a 1) exp))))
  (define (sumsOfPows a exp) (if (equal? exp 1)
    (sumOfPows a 1)
    (+ (sumOfPows a exp) (sumsOfPows a (- exp 1)))))
  (sumsOfPows 1 1)
  )
  """))
assert(interpProgram(testProg3) == SInt(1))
