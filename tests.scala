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

// vim: set ts=2 sw=2 et:
