#lang rosette/safe

(require
  (for-syntax syntax/parse)
  (only-in racket
           make-parameter
           parameterize)
  rosette/lib/angelic
  rosette/lib/destruct
  rosette/lib/synthax)

(struct plus () #:transparent)
(struct mult () #:transparent)
(struct primrec () #:transparent)

(struct dup () #:transparent)
(struct swap () #:transparent)
(struct dip () #:transparent)

(struct concat () #:transparent)
(struct map () #:transparent)

(struct lit (val) #:transparent)

(define (eval-word stack word)
  (destruct* (stack word)
             [((list a b c ...) (plus)) (cons (+ a b) c)]
             [((list a b c ...) (mult)) (cons (* a b) c)]
             [((list a b ...) (dup)) (cons a (cons a b))]
             [((list a b c ...) (swap)) (cons b (cons a c))]
             ; remember stack is in reverse
             [((list b a c ...) (concat)) (cons (append a b) c)]
             [((list f l s ...) (map))
              (destruct l
                        [(list) (cons '() s)]
                        [(list h t ...)
                         (destruct (apply eval (cons h s) f)
                                   [(list res s ...)
                                    (eval (cons f (cons t s)) (map) (lit (list res)) (swap) (concat))])])]
             [((list rec base n s ...) (primrec))
              (cond
                [(zero? n) (apply eval s base)]
                [else (apply eval (append (list rec base (- n 1) n) s) (primrec) rec)])] 
             [(_ (lit val)) (cons val stack)]
             [((list quot dipped s ...) (dip))
              (assert (list? quot) "quotation must be a list")
              (cons dipped (apply eval s quot))]
             [(_ _) (assert #f "evaluation stuck")]))

(define max-eval-recursion-depth (make-parameter 11))

(define (eval stack . words)
  (assert (> (max-eval-recursion-depth) 0) "eval recursion depth exceeded")
  (parameterize ([max-eval-recursion-depth (sub1 (max-eval-recursion-depth))])
    (destruct words
              [(list word words ...)
               (let ([stack (eval-word stack word)])
                 (apply eval stack words))]
              [(list) stack])))

(define-syntax (== stx)
  (syntax-parse stx
    [(_ name:id body:expr ...) #'(define name (list body ...))]))

(== square (dup) (mult))

(eval '() (lit '(1 2 3 4)) (lit (list (dup) (mult))) (map))
(eval '() (lit 5) (lit (list (lit 1))) (lit (list (mult))) (primrec))

(define-symbolic x y p q r s t u v w integer?)

(solve
 (assert (equal? (eval '() (lit y) (dup) (mult)) '(49))))

(synthesize
 #:forall (list x)
 #:guarantee (assert (equal? (eval '() (lit y) (lit x) (mult)) (list (+ x x)))))

#|(define (choose-from-list lst)
  (destruct lst|#

(define-grammar (words terminals)
  [word* (choose '() (cons (word) (word*)))]
  [word (choose
         (plus)
         (mult)
         ; (primrec) ; memory problems
         (dup)
         ;(concat)
         ;(map)
         (swap)
         ; quotation
         (lit (word*))
         (lit (terminal))
         (dip))]
  [terminal (apply choose* terminals)])

(define sketch
  (let ([vars (list w x)])
    (append (words vars #:depth 4) (list (plus)))))

(define M
  (synthesize
   #:forall (list x)
   #:guarantee (assert (equal? (apply eval '() sketch) (eval '() (lit x) (lit 10) (mult))))))

(evaluate sketch M)

; Stack Shuffling

(displayln "# Stack shuffling: rotate top 3 items on the stack")

; [x w v] | [swap] dip
; [w x v] | swap
; [w v x]
(define rot-3-sketch
  (words '() #:depth 3))

(evaluate rot-3-sketch
          (synthesize
           #:forall (list v w x)
           #:guarantee (assert (equal?
                                (apply eval (list v w x) rot-3-sketch)
                                (list x v w)))))

(define (quadratic a b c x)
  (+ (* a x x) (* b x) c))

(define-symbolic a* b* c* x* integer?)

(define quadratic-sketch (words (list a* b* c* x* x y p q v w) #:depth 20))

; (+ (* a x x) (* b x) c)
; (* a x x) (* b x) c + +
; a x x * * b x * c + +
; [a x] | dup * * b x * c + +
; [a x b] | [dup * *] dip x * c + + 
; [a x b] | [swap [dup] dip swap dup * *] dip
; [x a*x^2 b] | swap [*] dip c + +
; [c a x b] | [swap [dup] dip swap dup * *] dip swap [*] dip + +
; [c a b x] | swap ...
; [a c b x] | [[swap] dip] dip swap ...
; [a b c x] | [swap] dip [[swap] dip] dip swap ...

;(current-bitwidth 16)

; (unsat) is success
(verify (assert (equal? (eval (list x* a*) (dup) (mult) (mult)) (list (quadratic a* 0 0 x*)))))

#|(evaluate quadratic-sketch (synthesize
                            #:forall (list r s t u)
                            #:guarantee (assert (= (apply eval (list u t s r) quadratic-sketch)
                                                   (list (quadratic r s t u))))))|#