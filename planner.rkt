#lang racket
(require (lib "trace.ss"))

(define var? symbol?)

(define (apply-subst x e)
  (cond ((var? x) (let ((p (assoc x e))) (if p (cdr p) x)))
        ((pair? x) (cons (car x)(map (λ(y) (apply-subst y e)) (cdr x))))
        (else x) ))

(define (unify x y e)
  (define (extend-subst v x e)
    (cons (cons v x)
          (map (λ(p) (cons (car p) (apply-subst (cdr p) (list (cons v x))))) e)))  
  (define (occur v x)
    (or (and (var? x) (eq? v x))
        (and (pair? x)(ormap (λ(y) (occur v y)) (cdr x))) ))  
  (and e (let ((x (apply-subst x e))
               (y (apply-subst y e)))
           (cond ((equal? x y) e)
                 ((var? x) (and (not (occur x y)) (extend-subst x y e)))
                 ((var? y) (and (not (occur y x)) (extend-subst y x e)))
                 (else (and (pair? x) (pair? y) (=(length x) (length y))
                            (equal? (car x) (car y)) ; test if operator same
                            (foldl unify e (cdr x) (cdr y)) )) ))))

(define (freevarsin x)
  (cond ((var? x) (list x))
        ((pair? x) (remove-duplicates (append-map freevarsin (cdr x))))
        (else '()) ))

(define (make-var-generator v)
  (define n 0)
  (λ()(set! n(+ 1 n))
    (string->symbol(string-append
                    (symbol->string v) (number->string(- n 1)))) ))

(define (rename ids body fresh-id)
  (apply-subst body(map(λ(id) (cons id (fresh-id))) ids)))

(define (resolve s c)
  (define (equate x y e) ; returns '() or ( e )
    (let ((t (unify x y e))) (if t(list t) '())))
  (define (equate-lit x y t)
    (cond ((and (¬? x) (not (¬? y))) (equate(cadr x) y t))
          ((and (¬? y) (not (¬? x))) (equate x (cadr y) t))
          (else '()) ))
  ;(printf "node => ~a\n" s)
  (map (λ(th) (remove-duplicates (instantiate-clause(append (cdr c) (cdr s)) th)))
       (equate-lit (car c) (car s) '()) ))

(define (¬? x) (and (pair? x) (eq? (car x) '¬)))

(define (freevarsin-clause c)
  (remove-duplicates(append-map freevarsin c)))

(define (rename-clause c fresh-id)
  (cdr (rename (freevarsin-clause c) (cons 'or c) fresh-id)))

(define (instantiate-clause c e)
  (map (λ(p) (apply-subst p e)) c))

(define (ATP axioms ¬conjecs)
  (define (move-pos-lit-to-front c)
    (append (filter (λ(l)(not(¬? l))) c) (filter ¬? c)))
  (define +axioms (map move-pos-lit-to-front axioms))  
  ;(define fresh-id gensym) ;(make-var-generator 'x))
  (define fresh-id (make-var-generator 'x))
  (define (res-moves s)
    (append-map(λ(c) (map(λ(r) (list r c 1)) ; (s a w)
                         (resolve s (rename-clause c fresh-id))))
               +axioms))
  ;(define res-goal? null?)
  (define (goal? x) ; check if null or is just (¬(answer ...))
  (cond ((eq? x '()) #t)
        ((and (eq? 1 (length x)) (pair? x)) (eq? 'answer (first (car(cdr(car x))))))
        (else #f)) )
  ;(define (res-heuristic state) (printf "~a\n" state) (length (car state)))
  (define res-heuristic length)
  (A*-graph-search ¬conjecs goal? res-moves res-heuristic))

(require data/heap)
(define(A*-graph-search start goal? moves heuristic)
  (struct node (state pred move g h f))
  (define (node<=? x y) (<= (node-f x) (node-f y)))
  (define Q (make-heap node<=?))
  (define ht (make-hash))
  (define (not-in-hash? SAW) (eq? #f (hash-ref ht (get-hash (car SAW)) #f)))
  (define (print-solution anode)
    (cond
      [(null? anode)]
      [(null? (node-pred anode)) (list (list 'start (node-state anode) (node-g anode) (node-h anode) (node-f anode)))]
      [else (append (append (print-solution (node-pred anode))) (list (list (node-move anode) (node-state anode) (node-g anode) (node-h anode) (node-f anode))))]))
  (define (add-SAW-to-heap SAW prev)
    (let* [(weight (car (cdr (cdr SAW)))) (h (heuristic (car SAW))) (action (car (cdr SAW)))]
      (let [(g (if (null? prev) weight (+ weight (node-g prev))))]
        (define f (+ g h))
        (node (car SAW) prev action g h f))))
  (define (get-hash state) state)
  (define no-solution 'failure)
  
  (map (λ(x) (let [(h (heuristic x))] (heap-add! Q (node x '() 'start 0 h h)))) start)
  (let loop ()
    (define curr (heap-min Q))
    (hash-set! ht (get-hash (node-state curr)) curr)
    (heap-remove-min! Q)
    (cond
      [(goal? (node-state curr)) (print-solution curr)]
      [else
       (let ([SAWs (filter not-in-hash? (moves (node-state curr)))])
         (heap-add-all! Q (map (λ(x) (add-SAW-to-heap x curr)) SAWs)))
       (if (= (heap-count Q) 0) no-solution (loop))])))

(define block_axioms '(
                       ((poss(move b x y s)) (¬(on b x s)) (¬(clear b s)) (¬(clear y s))
                                             (¬(block b)) (¬(block y)) (¬(≠ b x)) (¬(≠ b y)) (¬(≠ x y)) )
                       ((on b y (move b x y s)) (¬(poss(move b x y s))) )
                       ((clear x (move b x y s)) (¬(poss(move b x y s))) )
                       ((on b2 x2(move b x y s)) (¬(on b2 x2 s)) (¬(≠ b2 b))
                                                 (¬(poss(move b x y s))))
                       ((clear y2(move b x y s)) (¬(clear y2 s)) (¬(≠ y2 y))
                                                 (¬(poss(move b x y s))))
                       
                       ((poss(movetotable b x s)) (¬(on b x s)) (¬(clear b s))
                                                  (¬(block b)) (¬(block x)) (¬(≠ b x)))

                       ((on b(t) (movetotable b x s)) (¬(poss(movetotable b x s))))
                       ((clear x (movetotable b x s)) (¬(poss(movetotable b x s))))
                       ((on b2 x2(movetotable b x s)) (¬(on b2 x2 s)) (¬(≠ b2 b))
                                                      (¬(poss(movetotable b x s))) )
                       ((clear y2(movetotable b x s)) (¬(clear y2 s)) (¬(≠ y2 (t)))
                                                      (¬(poss(movetotable b x s))) )
                       
                       ;;; distinct objects
                       ((≠(a)(b))) ((≠(b)(a)))
                       ((≠(a)(c))) ((≠(c)(a)))
                       ((≠(b)(c))) ((≠(c)(b)))
                       ((≠(a)(t))) ((≠(t)(a)))
                       ((≠(b)(t))) ((≠(t)(b)))
                       ((≠(c)(t))) ((≠(t)(c))) 
                       
                       ;;; blocks
                       ((block(a)))
                       ((block(b)))
                       ((block(c)))
                       
                       ;;; fluents for initial state 0
                       ((on(b)(t)0))
                       ((on(a)(t)0))
                       ((on(c)(a)0))
                       ((clear(b)0))
                       ((clear(c)0))
                       ))

(define conj '(((¬(on(a)(b)s)) (¬(on(b)(c)s)) (¬(answer s)) )))
(define conj1 '(((¬(on(b)(c)s)) (¬(answer s)) )))
(define conj2 '(((¬(on(a)(b)s)) (¬(answer s)) )))

;(trace resolve)
(time (ATP block_axioms conj1))