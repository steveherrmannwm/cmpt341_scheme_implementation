import sexp._

sealed abstract class Exp
case class Literal(v: SExp) extends Exp
case class Call(funcName : Exp, args : List[Exp]) extends Exp
case class Let(v : String,
               rhs: Exp,
               body : Exp) extends Exp
case class Ref(v : String) extends Exp
case class Conditional(cond: Exp, true_case: Exp, false_case: Exp) extends Exp
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
      case SList(exp) => Program(acc.reverse, parseExp(exp))
      case SCons(first, rest) =>{
        parseProgramHelper(rest, parseFunction(first) :: acc)
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
      case STrue() => Literal(STrue())
      case SFalse() => Literal(SFalse())
      case SInt(v) => Literal(SInt(v))
      case SSymbol("null") => Literal(SNil)
      case SList(SSymbol("quote"), exp) => Literal(exp)
      case SSymbol(id) => Ref(id)
      case SList(SSymbol("let"),
                 SList(SList(SSymbol(id), rhs)),
                 body) =>
        Let(id, parseExp(rhs), parseExp(body))
      case SList(SSymbol("lambda"), args, body) =>
        Lambda(parseArgs(args, List()), parseExp(body))
      case SList(SSymbol("if"), cond, t, f) =>
        Conditional(parseExp(cond), parseExp(t), parseExp(f))
      // If we're dealing with a function, we may not know how many arguments we're dealing with, so use a special function
      case function => function match {
        case SNil => throw new IllegalArgumentException("Illegal function call")
        // CAN ID BE ANYTHIN OTHER THAN A SSYMBOL?????
        case SCons(id, args) => {
          parseFunctionCall(parseExp(id), args, Nil)
        }
      }
    }
}

def parseFunctionCall(name: Exp, function: SExp, acc: List[Exp]) : Exp = {
  function match {
    case SNil => Call(name, acc.reverse)
    case SCons(first, rest) =>
      parseFunctionCall(name, rest, parseExp(first) ::acc)
  }
}

type Env = Map[String, SExp]
case class Closure(function: Exp, funcEnv: Box[Env]) extends SExp
case class Primitive(symbol: String) extends SExp

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

def interpExp(e: Exp, env : Env) : SExp = {
    e match {
        case Literal(v) => v
        case Call(f, e) => {
         val v1 = interpExp(f, env)
         val eargs = e.map {
           (e: Exp) => interpExp(e, env)
          }
          v1 match {
            case Closure(Lambda(args, body), funcEnv) =>{
              val v2 = eargs
              if(v2.length > args.length)
                throw new RuntimeException("Too many arguments given")
              else if(v2.length > args.length)
                throw new RuntimeException("Additional arguments required")
              val argVals = args zip v2
              val newEnv = funcEnv.contents.get ++ argVals.toMap
              interpExp(body, newEnv)
            }
            case Primitive("Add") => {
              eargs.foldLeft(SInt(0))((a,b) =>
                  (a,b) match {
                    case (SInt(lhs), SInt(rhs)) =>
                      SInt(lhs + rhs)
                    case _ => throw new RuntimeException("Can only add numbers")
                  })
            }
            case Primitive("Subtract") =>{
              val hd::tail = eargs
              val SInt(start) = hd
              val SInt(toSubtract) = tail.foldLeft(SInt(0))((a,b) =>
                  (a,b) match {
                    case (SInt(lhs), SInt(rhs)) =>
                      SInt(rhs + lhs)
                    case _ => throw new RuntimeException("Can only subtract numbers")
                  })
              SInt(start - toSubtract)
            }
            case Primitive("Multiply") =>{
              eargs.foldLeft(SInt(1))((a,b) =>
                  (a,b) match {
                    case (SInt(lhs), SInt(rhs)) =>
                      SInt(lhs * rhs)
                    case _ => throw new RuntimeException("Can only multiply numbers")
                  })
            }
            case Primitive("Null") => {
              // This function only accepts one argument, so assume that there is one
              val List(nul) = eargs
              nul match {
                case SNil => STrue()
                case _ => SFalse()
              }
            }
            case Primitive("Pair") => {
              val List(pair) = eargs
              pair match {
                case SCons(head, tail) => STrue()
                case _ => SFalse()
              }
            }
            case Primitive("cons") => {
              val arg1 = eargs(0)
              val arg2 = eargs(1)

              SCons(arg1, arg2)
            }
            case Primitive("cdr") => {
              val List(list) = eargs
              list match {
                case SCons(head, tail) => tail
                case _ => throw new RuntimeException("Expect pair as the argument")
              }
            }
            case Primitive("car") => {
              val List(list) = eargs
              list match {
                case SCons(head, tail) => head
                case _ => throw new RuntimeException("Expect pair as the argument")
              }
            }
            case Primitive("Equals") => {
              val arg1 = eargs(0)
              val arg2 = eargs(1)
              if (arg1 == arg2)
                STrue()
              else
                SFalse()
            }
          }
        }
        case Lambda(args, body) => {
          val envBox = new Box[Env]()
          envBox.contents = Some(env)
          Closure(Lambda(args, body), envBox)
        }
        case Ref(id) => {
          env.get(id) match {
            case None => throw new RuntimeException("unbound variable")
            case Some(v) => {
              v
            }
          }
        }
        case Let(id, rhs, body) =>{
            val rhsVal = interpExp(rhs, env)
            val newEnv = env + (id -> rhsVal)
            interpExp(body, newEnv)
        }
        case Conditional(cond, t, f) => {
          val condition = interpExp(cond, env)
          condition match {
                case SFalse() => interpExp(f, env)
                case _ => interpExp(t, env)
            }
        }
    }
}

val initialEnv : Env = Map(
  ("+" -> Primitive("Add")),
  ("-" -> Primitive("Subtract")),
  ("*" -> Primitive("Multiply")),
  ("cons" -> Primitive("cons")),
  ("car" -> Primitive("car")),
  ("cdr" -> Primitive("cdr")),
  ("pair?" -> Primitive("Pair")),
  ("null?" -> Primitive("Null")),
  ("equal?" -> Primitive("Equals"))
  )

def interpProgram(p : Program) : SExp = {
  val envBox = new Box[Env]()
  val mapped = p.defs.map {
    de => (de.name -> Closure(Lambda(de.arguments, de.body), envBox))
  }
  val funcMap = initialEnv ++ mapped.toMap
  envBox.contents = Some(funcMap)
  interpExp(p.exp, funcMap)
}
def evalExp(e : String) : SExp = interpExp(parseExp(parseSExp(e)), initialEnv)

def evalProgram(p : String) : SExp  ={
  interpProgram(parseProgram(parseSExp(p)))
}


// Arithmetic tests
val arithEx1 = parseExp(parseSExp("(* (- 5 2) 1)"))

// Let tests
val letEx1 = parseExp(parseSExp(
  """(let ((x 5))
       (+ x 7))"""))
assert(interpExp(letEx1, initialEnv) == SInt(12))

val letEx2 = parseExp(parseSExp(
  """(let ((x (+ 5 6)))
       (+ x 7))"""))
assert(interpExp(letEx2, initialEnv) == SInt(18))

val letEx3 = parseExp(parseSExp(
  """(let ((x (let ((y 1))
                 (+ y 2))))
        (+ x 3))"""))
assert(interpExp(letEx3, initialEnv) == SInt(6))
// Program parsing tests. We'll represent a program
// as a sequence of defintions, followed by a main

val progEx3 = parseProgram(parseSExp("""
 ((define (append l s)
      (if (null? l)
             s
                  (cons (car l) (append (cdr l) s))))
               (append (quote (1 2 3)) (quote (4 5 6))))
  """))
(evalExp(
  """
  (let ((two 2))
    (let ((double (lambda (n) (* n two))))
      (double 5)))
  """) == SInt(10))

(evalProgram(
  """
  ((define (myf arg)
     (+ arg 1))
    (define (apply f)
         (f 4))
        (apply myf))
  """
) == SInt(5))

assert(evalProgram(
  """
  ((define (foldLeft f l acc)
     (if (null? l)
            acc
                 (foldLeft f (cdr l) (f (car l) acc))))
              (foldLeft + (quote (1 2 3)) 0))
  """) == SInt(6))

// Returns the sum of the power sums of a given x and n from n to 0
// Only works with positive integers for x and n
// x must also be at least 1

val testProg1 = parseProgram(parseSExp("""
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
assert(interpProgram(testProg1) == SInt(1))
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
  (sumsOfPows 3 3)
  )
  """))
assert(interpProgram(testProg2) == SInt(56))

// FINAL TESTS
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

