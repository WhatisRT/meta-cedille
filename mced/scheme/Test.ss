#! scheme --script
(load "Bootstrap/DSum.ss")
(load "Bootstrap/Product.ss")
(load "Bootstrap/Nat.ss")
(load "SchemeCompiler/Test.ss")

(define evalNat (lambda (n) (((n 'nat) 0) (lambda (x) (+ 1 x)))))

(for-each
 (lambda (x) (display (evalNat (square (eval x)))) (newline))
 '(one two three four))
