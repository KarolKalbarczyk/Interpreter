# Interpreter
This project i interpreter for Scheme-like language in Haskell, there are eval functions written using both monad transformers and normal monads.
Syntax:
accesible literals are booleans, integers and strings
Arrays are defined with [], no commas between elements
Every expressions must be engulfed in () brackets
Mathematical operations are written in polish notation
Special syntax is
  (lambda (arguments) (expression)) e.q. (lambda (x y) (+ x (* y 4))
  (begine (definitions) (expression)) e.q. (begin (define x 6) (define y 7) (+ x y))
  (let (pairs of variables and values) (expression)) e.q. (let (x 5 y (- 9 7)) (+ x y))
  ((x) 5) is application of x to argument 5, blows up if x is not a lambda
  (if predicate expr expr) - same as in all languages
  (map lambda fun) - works same as fmap on list in Haskell
  


Example program:
(map (lambda (u) (+ u 1)) [1 2 3 (begin (define x 5) (define y 2) (* x (((lambda (z) (* z z)) y))))])
will return [2 3 4 21]

In order to run you have to build dependencies using cabal build, and then run in in ghci, use method main for repl.
