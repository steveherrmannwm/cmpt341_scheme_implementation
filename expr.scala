import sexp._

sealed abstract class Exp
case class Literal(v: SExp) extends Exp
case class Add(lhs: Exp, rhs: Exp) extends Exp
case class Subtract(lhs: Exp, rhs: Exp) extends Exp
case class Multiply(lhs: Exp, rhs: Exp) extends Exp
case class Call(funcName : Exp, args : List[Exp]) extends Exp
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
case class Lambda(args: List[String], body: Exp) extends Exp

case class Def(name : String, arguments : List[String], body : Exp)
case class Program(defs : List[Def], exp : Exp)

class Box[A] {
  var contents : Option[A] = None
}

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
      case SSymbol(id) => Ref(id)
      case SList(SSymbol("let"),
                 SList(SList(SSymbol(id), rhs)),
                 body) =>
        Let(id, parseExp(rhs), parseExp(body))
      case SList(SSymbol("lambda"), SList(args), body) =>
        Lambda(parseArgs(args, List()), parseExp(body))
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
        case SCons(id, args) => {
          parseFunctionCall(id, args, Nil)
        }
      }
    }
}

def parseFunctionCall(name: SExp, function: SExp, acc: List[Exp]) : Exp = {
  function match {
    case SNil => Call(parseExp(name), acc.reverse)
    case SCons(first, rest) =>
      parseFunctionCall(name, rest, parseExp(first) ::acc)
  }
}

type Env = Map[String, Box[SExp]]
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

/*def interpFuncArgs(argNames : List[String], argVals : List[Exp], acc: Env, env: Env, functions : List[Def]) : Map[String, SExp] = {
  (argNames, argVals) match {
    case (Nil, Nil) => {
      acc
    }
    case (argName :: args, argVal :: vals) => {
      interpFuncArgs(args, vals, acc + (argName -> new Box(Some(interpExp(argVal, env, functions)))), env, functions)
    }
   case (Nil, head :: tail) => throw new RuntimeException("Too many arguments were called for the function")
    case (head:: tail, Nil) => throw new RuntimeException("Function missing required arguments")
  }
}
*/
def interpExp(e: Exp, env : Env) : SExp = {
    e match {
        case Literal(v) => v
        case Call(f, eargs) => {
          val v1 = interpExp(f, env)
          val vargs = eargs.map {
            (e: Exp) => interpExp(e, env)
          }
          v1 match {
            case Closure(Lambda(args, body), storedEnv) => {
              if(args.length > vargs.length)
                throw new RuntimeException("Not enough arguments given")
              else if(args.length < vargs.length)
                throw new RuntimeException("Too many arguments given")
              val boxedArgs = vargs.map {
                a => (a._1, new Box().contents)
              }
              val argsList = args zip vargs
              val argsMap = argsList.toMap

              interpExp(body, env ++ argsMap)
            }
            case Primitive("+") =>{
              val SInt(arg0) = vargs(0)
              val SInt(arg1) = vargs(1)
              SInt(arg0 + arg1)
            }
            case Primitive("*") =>{
              val SInt(arg0) = vargs(0)
              val SInt(arg1) = vargs(1)
              SInt(arg0 + arg1)
            }
            case Primitive("-") =>{
              val SInt(arg0) = vargs(0)
              val SInt(arg1) = vargs(1)
              SInt(arg0 + arg1)
            }
            case _ => throw new RuntimeException("Tried to call a non-function")
          }
        }
        case Lambda(args, body) => Closure(Lambda(args, body), env)
        case Ref(id) =>{
          env.get(id) match {
            case None => throw new RuntimeException("unbound variable")
            case Some(v) => {
             v
            }
          }
        }
        case Let(id, rhs, body) =>{
            val rhsVal = interpExp(rhs, env)
            val cons = new Box()
            cons.content = Some(rhsVal)
            val newEnv = env + (id -> cons)
            interpExp(body, newEnv)
        }
        case Conditional(cond, t, f) => {
          val condition = interpExp(cond, env)
          condition match {
                case SInt(a) =>
                  if (a > 0)
                    interpExp(t, env)
                  else
                    interpExp(f, env)
                case STrue() => interpExp(t, env)
                case SFalse() => interpExp(f, env)
                case _ => throw new RuntimeException("unable to parse conditional")
            }
        }
        case Equal(l,r) => {
          val lv = interpExp(l, env)
          val rv = interpExp(r, env)
          if(lv == rv)
            STrue()
          else
            SFalse()
        }
      case GreaterThan(l, r) => {
        val lv = interpExp(l, env)
        val rv = interpExp(r, env)
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
        val lv = interpExp(l, env)
        val rv = interpExp(r, env)
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
        val lv = interpExp(l, env)
        val rv = interpExp(l, env)
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
        val lv = interpExp(l, env)
        val rv = interpExp(l, env)
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
        SCons(interpExp(l, env), interpExp(r, env))
      }
      case Car(exp) =>
      {
        val l = interpExp(exp, env)
        l match {
          case SNil => throw new RuntimeException("Structure given to car wasn't a pair")
          case SCons(head, tail) => {
            head
          }
        }
      }
      case Cdr(exp) => {
        val l = interpExp(exp, env)
        l match {
          case SNil => throw new RuntimeException("structure given to Cdr wasn't a pair")
          case SCons(head, tail) => tail
        }
      }
      case Pair(exp) => {
        val l = interpExp(exp, env)

        l match {
          case SList(a) => STrue()
          case _ => SFalse()
        }
      }
      case Null(exp) => {
        val l = interpExp(exp, env)
        l match {
          case SNil => STrue()
          case _ => SFalse()
        }
      }
    }
}

val initialEnv : Env = Map(
    "+" -> new Box(Some(Primitive("+"))),
    "*" -> new Box(Some(Primitive("*"))),
    "-" -> new Box(Some(Primitive("-")))
  )

def interpProgram(p : Program) : SExp = {
  // Parse our defintions from the program into the intial env
  val funcs = p.defs map {
    item => List(item.name -> new Box(Closure(Lambda(item.arguments, item.body), None)))
  }
  // Add all of our functions to the environment
  val funcEnv = initialEnv zip funcs.toMap()
  // Remap our functions with the new environment which contains all of the functions
  val funcs = p.defs map {
    item => List(item.name -> new Box(Some(Closure(Lambda(item.arguments, item.body), funcEnv))))
  }

  val startEnv = initialEnv zip funcs.toMap()
  interpExp(p.exp, startEnv)
}
def evalExp(e : String) : SExp = interpExp(parseExp(parseSExp(e)), initalEnv, List())

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
// Tests for completed interpreter
// Math

assert(
  evalProgram(
  """
  (
    (* (+ 1 2) 4)
  )
  """
  )
==
SInt(12)
)

// Let

assert(
  evalProgram(
  """
  (
    (let ((x (+ 1 2)))
      (* x 4))
  )
  """
  )
==
SInt(12)
)

assert(
  evalProgram(
  """
  (
    (let ((x (let ((y 1))
               (+ y 2))))
      (* x 4))
  )
  """
  )
==
SInt(12)
)

assert(
  evalProgram(
  """
  (
    (let ((x 2))
      (let ((y 4))
        (let ((x 3))
          (* x y))))
  )
  """
  )
==
SInt(12)
)

// Lists

assert(
  evalProgram(
  """
  (
    null
  )
  """
  )
==
SNil
)

assert(
  evalProgram(
  """
  (
    (let ((x null))
      (null? x))
  )
  """
  )
==
STrue()
)

assert(
  evalProgram(
  """
  (
    (let ((x null))
      (pair? x))
  )
  """
  )
==
SFalse()
)

assert(
  evalProgram(
  """
  (
    (let ((l (cons 1 2)))
      (car l))
  )
  """
  )
==
SInt(1)
)

assert(
  evalProgram(
  """
  (
    (let ((l (cons 1 2)))
      (cdr l))
  )
  """
  )
==
SInt(2)
)

assert(
  evalProgram(
  """
  (
    (let ((l (cons 1 2)))
      (pair? l))
  )
  """
  )
==
STrue()
)

assert(
  evalProgram(
  """
  (
    (let ((l (cons 1 2)))
      (null? l))
  )
  """
  )
==
SFalse()
)

assert(
  evalProgram(
  """
  (
    (null? 5)
  )
  """
  )
==
SFalse()
)

assert(
  evalProgram(
  """
  (
    (pair? 5)
  )
  """
  )
==
SFalse()
)

// Conditionals

assert(
  evalProgram(
  """
  (
    (let ((c #f))
      (if c 5 6))
  )
  """
  )
==
SInt(6)
)

assert(
  evalProgram(
  """
  (
    (let ((c (cons 1 2)))
      (if c 5 6))
  )
  """
  )
==
SInt(5)
)

assert(
  evalProgram(
  """
  (
    (let ((c #t))
      (if c 5 6))
  )
  """
  )
==
SInt(5)
)

assert(
  evalProgram(
  """
  (
    (let ((v1 5))
      (equal? v1 5))
  )
  """
  )
==
STrue()
)

assert(
  evalProgram(
  """
  (
    (let ((v1 5))
      (equal? v1 6))
  )
  """
  )
==
SFalse()
)

assert(
  evalProgram(
  """
  (
    (let ((v1 #f))
      (equal? v1 #f))
  )
  """
  )
==
STrue()
)


// Define

assert(
  evalProgram(
  """
  (
    (define (f)
      5)
    (f)
  )
  """
  )
==
SInt(5)
)

assert(
  evalProgram(
  """
  (
    (define (f arg)
      (+ 1 arg))
    (f 5)
  )
  """
  )
==
SInt(6)
)

assert(
  evalProgram(
  """
  (
    (define (g) 1)
    (define (f arg)
      (+ (g) arg))
    (f 5)
  )
  """
  )
==
SInt(6)
)

// Checks that reference to variable by dynamic scope is an error;
// you should implement lexical scope.
assert(
  try {
    evalProgram(
      """
      (
        (define (g) x)
        (define (f x)
          (g))
        (f 5)
      )
    """)
    false
 } catch {
   case e: Exception => true
 }
)

// Lambda

assert(evalProgram(
  """
  ((let ((double (lambda (n) (* n 2))))
    (double 5)))
  """) == SInt(10))

assert(evalProgram(
  """
  ((let ((two 2))
    (let ((double (lambda (n) (* n two))))
      (double 5))))
  """) == SInt(10))

assert(evalProgram(
  """
  ((((lambda (x) (lambda (y) x))
    5)
   6))
  """)
  == SInt(5))

assert(evalProgram(
  """
  ((let ((twice (lambda (f) (lambda (arg) (f (f arg))))))
    ((twice (lambda (x) (* x 2))) 5)))
  """)
  == SInt(20))

// Higher-order primitives

assert(evalProgram(
  """
  ((let ((apply (lambda (f) (f 3 4))))
     (cons (apply +)
           (apply cons))))
  """
) == SCons(SInt(7), SCons(SInt(3), SInt(4))))

assert(evalProgram(
  """
  ((define (foldLeft f l acc)
   (if (null? l)
     acc
     (foldLeft f (cdr l) (f (car l) acc))))
 (foldLeft + (quote (1 2 3)) 0))
 """)
 == SInt(6))

// Real programs

assert(
  evalProgram("""
  ((define (append l s)
   (if (null? l)
     s
     (cons (car l) (append (cdr l) s))))
   (append (quote (1 2 3)) (quote (4 5 6))))

  """)
  ==
  SList(SInt(1), SInt(2), SInt(3), SInt(4), SInt(5), SInt(6))
)

assert(
  evalProgram(
    """
    (
    (define (even? n)
      (if (equal? n 0)
        #t
        (odd? (- n 1))))
    (define (odd? n)
      (if (equal? n 0)
        #f
        (even? (- n 1))))
    (even? 10)
    )
    """)
  ==
  STrue()
)

// If you're curious what this is, dig in here!
// http://matt.might.net/articles/compiling-up-to-lambda-calculus/
assert(evalProgram(
  """
  ((define (succ n) (+ n 1))
   (define (natify church-numeral)
     ((church-numeral succ) 0))
   (natify ((lambda (f) (f (lambda (f) (lambda (z) (f (f (f (f (f z)))))))))
      (((lambda (y) (lambda (F) (F (lambda (x) (((y y) F) x)))))
        (lambda (y) (lambda (F) (F (lambda (x) (((y y) F) x))))))
      (lambda (f)
        (lambda (n)
          ((((((lambda (n)
            ((n (lambda (_) (lambda (t) (lambda (f) (f (lambda (void) void))))))
              (lambda (t) (lambda (f) (t (lambda (void) void))))))
            (((lambda (n)
              (lambda (m)
                ((m
                  (lambda (n)
                    (lambda (f)
                      (lambda (z)
                        (((n (lambda (g) (lambda (h) (h (g f)))))
                          (lambda (u) z))
                        (lambda (u) u))))))
                      n)))
                    n)
                  (lambda (f) (lambda (z) z))))
                (lambda (_)
                  ((lambda (n)
                    ((n (lambda (_) (lambda (t) (lambda (f) (f (lambda (void) void))))))
                      (lambda (t) (lambda (f) (t (lambda (void) void))))))
                    (((lambda (n)
                      (lambda (m)
                        ((m
                          (lambda (n)
                            (lambda (f)
                              (lambda (z)
                                (((n (lambda (g) (lambda (h) (h (g f)))))
                                  (lambda (u) z))
                                (lambda (u) u))))))
                              n)))
                            (lambda (f) (lambda (z) z)))
                          n))))
                        (lambda (_) (lambda (t) (lambda (f) (f (lambda (void) void))))))
                      (lambda (_) (lambda (f) (lambda (z) (f z)))))
                    (lambda (_)
                      (((lambda (n) (lambda (m) (lambda (f) (lambda (z) ((m (n f)) z))))) n)
                        (f
                          (((lambda (n)
                            (lambda (m)
                              ((m
                                (lambda (n)
                                  (lambda (f)
                                    (lambda (z)
                                      (((n (lambda (g) (lambda (h) (h (g f)))))
                                        (lambda (u) z))
                                      (lambda (u) u))))))
                                    n)))
                                  n)
                                (lambda (f) (lambda (z) (f z))))))))))))))
                              """
                            )
                          == SInt(120))


