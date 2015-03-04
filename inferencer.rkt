#lang racket

(require "mk/mk.rkt")

(define-syntax test
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Testing ~s\n" title)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (printf "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
                     'tested-expression expected produced)))))))

(define top-prop 'tt)
(define bot-prop 'ff)
(define (is-prop t v path)
  `(is ,t ,v . ,path))

(define (not-prop t v path)
  `(not ,t ,v . ,path))

(define (Un . ts)
  `(U ,@ts))

(define Bot 'Nothing)
(define Top 'Any)
(define Num 'Num)
(define Bool 'Bool)

(define (booleano b)
  (conde
    [(== #t b)]
    [(== #f b)]))

(define empty-object 'empty)
;(define (path v ))

(define (-val v) `(val ,v))

(define (-or p1 p2)
  `(or ,p1 ,p2))

(define (oro p1 p2 o)
  (conde
   [(== p1 p2) (== o p1)]
   [(=/= p1 p2) (== bot-prop p1) (== o p2)]
   [(=/= p1 p2) (== bot-prop p2) (== o p1)]
   [(fresh (l1 r1)
           (== (-or l1 r1) p1)
           (=/= l1 p2)
           (=/= r1 p2)
           (== (-or p1 p2) o))]
   [(fresh (l1 r1)
           (== (-or l1 r1) p2)
           (=/= l1 p1)
           (=/= r1 p1)
           (== (-or p1 p2) o))]
   [(fresh (l1 l2 r1 r2)
           (=/= p1 p2)
           (=/= (-or l1 r1) p1)
           (=/= (-or l2 r2) p2)
           (== (-or p1 p2) o))]))

;; return an object that is a common superobject of both
(define (common-objo o1 o2 o)
  (conde
   [(== o1 o2) (== o o1)]
   [(=/= o1 o2) (== o empty-object)]))

;; update G with prop, returning a new env G^
(define (env+ G prop G^)
  (conde
    [(== G '()) (== `(,prop) G^)]
    [(fresh (a d G^^ t1 t2 v path)
            (== G `(,a . ,d))
            ;; env can have bot
            ;; (=/= a bot-prop)
            (=/= a top-prop)
            ;; if a is is-prop then use update
            (conde
             [(== (is-prop t1 v path) a)
              (conde
               ;; only use update if it gives a type different than the current prop
               ;; since we add the prop to the environment at the end.
               [(fresh (t3)
                       (== (is-prop t2 v path) prop)
                       (conde
                        [(=/= t1 t2)
                         (=/= t2 t3)
                         (updateo #t t1 t2 path t3)
                         (== G^ `(,(is-prop t3 v path) . ,G^^))]
                        ;; drop proposition since we're adding `prop` at the end
                        [(== t1 t2)
                         (== G^ G^^)]))]
               [(fresh (t3)
                       (== (not-prop t2 v path) prop)
                       (conde
                        [(=/= t2 t3)
                         (updateo #f t1 t2 path t3)
                         (== G^ `(,(is-prop t3 v path) . ,G^^))]
                        ;; drop proposition since we have a contradiction
                        [(== t1 t2)
                         (== G^ G^^)]))]
               ;; just pass `a` on
               [(== G^ `(,a . ,G^^))])])
            (env+ d prop G^^))]))

;; apply prop to each G
(define (extend-envo G prop G^)
  (conde
   [(== top-prop prop)
    (== G G^)]
   [(== bot-prop prop)
    (== G^ `(,bot-prop))]
   [(env+ G prop G^)]))

(define (type-conflicto t1 t2 b)
  (conde
   [(== t1 t2)
    (== b #f)]
   [(subtypeo t1 t2)
    (== b #f)]
   [(subtypeo t2 t1)
    (== b #f)]
   [(== b #t)
    (=/= t1 t2)]))

(define (proves*o venv prop-env prop)
  (conde
   [(== prop-env '())
    (== top-prop prop)]
   [(fresh (a d)
           (== prop-env `(,a . ,d))
           (conde
            [(== bot-prop a)]
            ;; this case is handled at the end of the proves*o
            ;[(== top-prop prop)]
            [(fresh (t1 t2 v p)
                    (== (is-prop t1 v p) a)
                    (== (is-prop t2 v p) prop)
                    (subtypeo t1 t2))]
            [(fresh (t1 t2 v p)
                    (== (not-prop t1 v p) a)
                    (== (not-prop t2 v p) prop)
                    (subtypeo t2 t1))]
            [(=/= bot-prop a)
             (proveso d prop)]))]))

(define (proveso prop-env prop)
  (proves*o '() prop-env prop))

(define (subobjo o1 o2)
  (conde
   [(== o1 o2)]
   [(=/= o1 o2)
    (== empty-object o2)]))

; Succeed if child-type is a subtype of parent-type,
; like (var #f) is a subtype of Bool.
(define (subtypeo child-type parent-type)
  (conde
    [(== child-type parent-type)]
    [(== Bot child-type)
     (=/= Bot parent-type)]
    [(=/= child-type parent-type)
     (=/= Bot child-type)
     (conde
      [(== parent-type Top)]
      [(fresh (b)
              (== (-val b) child-type)
              (conde
               [(booleano b)
                (== Bool parent-type)]
               [(numbero b)
                (== Num parent-type)]))]
      [(fresh (arg1 ret1 v1+ v1- o1 arg2 ret2 v2+ v2- o2)
              (== `(,arg1 -> ,ret1 ,v1+ ,v1- ,o1) child-type)
              (== `(,arg2 -> ,ret2 ,v2+ ,v2- ,o2) parent-type)
              (subobjo o1 o2)
              (proveso v2+ v1+)
              (proveso v2- v1-)
              (subtypeo arg2 arg1)
              (subtypeo ret1 ret2))]
      [(fresh (t1 t2)
              (== (Un t1 t2) child-type)
              (=/= t1 t2)
              (=/= Bot t1)
              (=/= Bot t2)
              (subtypeo t1 parent-type)
              (subtypeo t2 parent-type))]
      [(fresh (t1 t2)
              (== (Un t1 t2) parent-type)
              (=/= t1 t2)
              (=/= Bot t1)
              (=/= Bot t2)
              (conde
               [(subtypeo child-type t1)]
               [(subtypeo child-type t2)]))])]))

(test "subtype function"
      (run 1 (q)
           (subtypeo q `(Num -> Num tt tt empty)))
      '((Num -> Num tt tt empty)))

(test "subtype function contra"
      (run 1 (q)
           (subtypeo '(Num -> Num tt tt empty) '((val #f) -> Num tt tt empty)))
      '(_.0))

(define (Uno s t r)
  (conde
   [(fresh (l1 r1)
           (== (Un l1 r1) s)
           (=/= l1 t)
           (=/= r1 t)
           (== r (Un s t)))]
   [(fresh (l1 r1)
           (== (Un l1 r1) t)
           (=/= l1 s)
           (=/= r1 s)
           (== r (Un s t)))]
   [(subtypeo s t)
    (== r s)]
   [(subtypeo t s)
    (== r t)]
   [(fresh (l1 l2 r1 r2)
           (== r (Un s t))
           (=/= (Un l1 r1) s)
           (=/= (Un l2 r2) t))]))

(define (refineso s t b)
  (conde
   [(== #t b)
    (subtypeo s t)]))

(define (removeo s t r)
  (conde
   [(fresh (s1 s2 r1 r2)
           (== (Un s1 s2) s)
           (Uno r1 r2 r)
           (removeo s1 t r1)
           (removeo s2 t r2))]
   [(subtypeo s t)
    (== r Bot)]))
  
(define (restricto s t r)
  (conde
   [(fresh (s1 s2 r1 r2)
           (== (Un s1 s2) s)
           (Uno r1 r2 r)
           (restricto s1 t r1)
           (restricto s2 t r2))]
   [(subtypeo s t)
    (== r s)]))
  
(define (updateo pol s t p r)
  (conde
   [(== '() p)
    (== #t pol)
    (restricto s t r)]
   [(== '() p)
    (== #f pol)
    (removeo s t r)]))

(define (membero l e)
  (fresh (a d)
         (== l `(,a . ,d))
         (conde
          [(== e a)]
          [(membero d e)])))

(define (not-membero l e)
  (conde
   [(== '() l)]
   [(fresh (a d)
           (== l `(,a . ,d))
           (=/= a e)
           (not-membero d e))]))

(define (check-belowo G t1 v1+ v1- o1 t2 v2+ v2- o2)
  (fresh (G+ G-)
         (conde
          [(membero G bot-prop)]
          [(not-membero G bot-prop)
           (subobjo o1 o2)
           (extend-envo G v1+ G+)
           (extend-envo G v1- G-)
           (subtypeo t1 t2)
           (proveso G+ v2+)
           (proveso G- v2-)])))
  
; Under proposition environment G, expression e has type t,
; 'then' proposition v+, 'else' proposition v- and object o.
(define (infer G e t v+ v- o)
  (conde
    ; T-False
    ; G |- #f : (val #f) ; ff | tt ; empty
    [(fresh (G+ G-)
            (== #f e)
            (check-belowo G
                          (-val #f) bot-prop top-prop empty-object
                          t         v+       v-       o))]
    ; T-True
    ; G |- #t : (val #t) ; tt |ff ; empty
    [(fresh (G+ G-)
            (== #t e)
            (check-belowo G
                          (-val #t) top-prop bot-prop empty-object
                          t         v+       v-       o))]
    ; T-Num
    ; G |- n : (val n) ; tt |ff ; empty
    [(fresh (G+ G- n)
            (numbero e)
            (== n e)
            (check-belowo G
                          (-val n) top-prop bot-prop empty-object
                          t        v+       v-       o))]
    ; T-If
    ; G      |- e1 : t1 ; v1+ | v1- ; o1
    ; G, v1+ |- e2 : t  ; v2+ | v2- ; o
    ; G, v1- |- e3 : t  ; v3+ | v3- ; o
    ; ----------------------------------------------
    ; G |- (if e1 e2 e3) : t ; v2+ v v3+ | v2- v v3- ; o
    [(fresh (e1 e2 e3 tb1 tb2 G2 G3 G+ G-
             t1 v1+ v1- v2+ v2- v3+ v3- o o1 o2 o3)
       (== `(if ,e1 ,e2 ,e3) e)
       
       (infer G e1 t1 v1+ v1- o1)
       (extend-envo G v1+ G2)
       (extend-envo G v1- G3)
       (infer G2 e2 tb1 v2+ v2- o2)
       (infer G3 e3 tb2 v3+ v3- o3)
       
       (fresh (tact v+act v-act oact)
              (Uno tb1 tb2 tact)
              (oro v2+ v3+ v+act)
              (oro v2- v3- v-act)
              (common-objo o2 o3 oact)
              ;; this probably goes here
              (check-belowo G
                            tact v+act v-act oact
                            t    v+    v-    o)))]
    ; T-Abs
    ; G, s_x |- e1 ; t1 ; v1+ | v1- ; o1
    ; -----------------------------------------------------------------------
    ; G |- (lambda (x : s) e1) : (s -> t1 ; v1+ | v1- ; o1) ; tt | ff ; empty
    [(fresh (x s e1 t1 v1+ v1- o1 G+ G-)
       (== `(lambda (,x : ,s) ,e1) e)
       (check-belowo G
                     `(,s -> ,t1 ,v1+ ,v1- ,o1) top-prop bot-prop empty-object
                     t                          v+       v-       o)
       (infer `(,(is-prop s x '()) . ,G) e1 t1 v1+ v1- o1))]
    ; T-Var
    ; G |- t_x
    ; ---------------------------------------------------
    ; G |- x : t ; (not (val #f) x) | (is (val #f) x) ; x
    [(fresh (x t1 G+ G-)
       (symbolo e)
       (== x e)
       ; use t here because proveso uses subtyping
       (proveso G (is-prop t x '()))
       (check-belowo G
                     t (not-prop (-val #f) x '()) (is-prop  (-val #f) x '()) x
                     t v+                         v-                         o))]
    ; T-Inc
    ; G |- e1 : num ; v1+ | v1- ; o1
    ; -------------------------------------
    ; G |- (inc e1) : num ; tt | ff ; empty
    [(fresh (e1 G+ G-)
       (== `(inc ,e1) e)
       ;; this should be an easy check
       (infer G e1 Num top-prop top-prop empty-object)
       (check-belowo G
                     Num  top-prop bot-prop empty-object
                     t    v+       v-       o))]
    [(fresh (e1 t1)
            (== `(ann ,e1 ,t1) e)
            (infer G e1 t1 v+ v- o)
            (subtypeo t1 t))]
    [(fresh (e1 t1 v1+ v1- o1 G+ G-)
            (== `(ann ,e1 ,t1 ,v1+ ,v1- ,o1) e)
            (check-belowo G
                          t1 v1+ v1- o1
                          t  v+  v-  o))]))

(test "proveso"
      (run 1 (q)
           (proveso '() top-prop))
      '(_.0))

(test "proveso"
      (run 1 (q)
           (proveso '() bot-prop))
      '())


(test "bad proveso" 
      (run 1 (q) (proveso `(,top-prop) bot-prop))
      '())

(test "proveso"
      (run 1 (q)
           (proveso '(,top-prop) q))
      '(tt))

(test "proveso"
      (run 1 (q)
           (proveso '(,bot-prop) q))
      '(tt))

(test "simple (val #t) proves"
      (run 1 (q)
           (subtypeo (-val #t) q)
           )
      '((val #t)))

(test "proves"
      (run 1 (q)
           (fresh (G t v+ v- G+ G-)
                  (== G '())
                  (== v+ bot-prop)
                  (== v- top-prop)
                  (extend-envo G top-prop G+)
                  (proveso G+ v+)
                  (extend-envo G bot-prop G-)
                  (proveso G- v-)
                  (subtypeo (-val #t) t)
                  ))
      '())

(test "subobjo"
      (run 1 (q)
           (subobjo empty-object q))
      '(empty))

(test "plain #t, fresh props and o"
      (run 1 (q)
           (fresh (v+ v- o)
                  (infer '() #t q v+ v- o)))
      '((val #t)))

(test "plain #t, fresh v- and o"
      (run 1 (q)
           (fresh (v+ v- o)
                  (infer '() #t q top-prop v- o)))
      '((val #t)))

(test "plain #t, fresh o"
      (run 1 (q)
           (fresh (v+ v- o)
                  (infer '() #t q top-prop top-prop o)))
      '((val #t)))

(test "plain #t, fresh o"
      (run 1 (q)
           (fresh (v+ v- o)
                  (infer '() #t q top-prop bot-prop o)))
      '((val #t)))

(test "plain #t"
  (run 1 (q)
    (infer '() #t q top-prop bot-prop empty-object))
  '((val #t)))

(test "good plain #f"
  (run 1 (q)
    (infer '() #f q bot-prop top-prop empty-object))
  '((val #f)))

(test "good plain #f"
  (run 1 (q)
    (infer '() #f q top-prop top-prop empty-object))
  '((val #f)))


(test "bad plain #f concrete type"
  (run 1 (q)
       (fresh (v+) 
              (infer '() #f (-val #f) top-prop bot-prop empty-object)))
  '())

;; TODO 
;(test "bad plain #f variable type"
;  (run 1 (q)
;       (fresh (v+) 
;              (infer '() #f q top-prop bot-prop empty-object)))
;  '())

(test "if, type #t"
  (run 1 (q)
    (fresh (v+ v- o)
           (infer '() '(if #t #t #t) q v+ v- o)))
  '((val #t)))

(test "if, type #t"
  (run 1 (q)
    (fresh (v+ v- o)
           (infer '() '(if #t #t #f) q v+ v- o)))
  `(,(Un (-val #t) (-val #f))))

(test "bad Bot"
  (run 1 (q)
    (fresh (v+ v- o)
           (infer `(,top-prop) #t Bot v+ v- o)))
  '())

(test "bot-prop proves anything"
  (run 1 (q)
    (fresh (v+ v- o)
           (infer `(,bot-prop) #t Bot v+ v- o)))
  `(_.0))

(test "bad Bot in empty env"
  (run 1 (q)
    (fresh (v+ v- o)
           (infer `() #t Bot v+ v- o)))
  `())

(test "if, unreachable else branch"
      (run 1 (q)
           (fresh (v+ v- o)
                  (infer '() '(if #t #t 1) (-val #t) v+ v- o)))
      '(_.0))

(test "simulate if, unreachable else branch bad type"
      (run 1 (q)
           (fresh (v+ v- o)
                  (infer `(,bot-prop) '1 Bot top-prop top-prop empty-object)))
      '(_.0))

(test "simulate bad if, unreachable else branch bad type"
      (run 1 (q)
           (fresh (v+ v- o)
                  (infer `(,top-prop) #t Bot top-prop top-prop empty-object)))
      '())

(test "proveso top-prop should only return one answer"
      (run* (q)
           (fresh (v+ v- o)
                  (proveso `(,top-prop) q)))
      '(tt))

(test "if, unreachable else branch bad type"
      (run 1 (q)
           (fresh (v+ v- o)
                  (infer '() '(if #t #t 1) Bot top-prop top-prop empty-object)))
      '())

(test "another if, type #t"
  (run 1 (q)
    (infer '() '(if #f #t #t) q top-prop top-prop empty-object))
  '((val #t)))

(test "another if, bad then-prop"
  (run 1 (q)
    (infer '() '(if #f #t #t) q bot-prop top-prop empty-object))
  '())

(test "if, union #t #f"
  (run 1 (q)
    (infer '() '(if #t #t #f) q top-prop top-prop empty-object))
  '(bool))


(test "plain number"
  (run 1 (q)
    (infer '() 1 q top-prop top-prop empty-object))
  '((val 1)))

(test "if, type (val 1)"
  (run 1 (q)
    (infer '() '(if #t 1 1) q top-prop top-prop empty-object))
  '((val 1)))

(test "if, type (val 1)"
  (run 1 (q)
    (infer '() '(if #t 1 1) Num top-prop top-prop empty-object))
  '(_.0))


(test "inc should accept a number and return a number"
  (run 1 (q)
    (infer '() '(inc 1) q top-prop top-prop empty-object))
  '(num))

(test ""
      (run 1 (q)
           (subtypeo (-val #f) Num))
      '())


(test "assign bad type to #t"
  (run 1 (q)
       (fresh (G e t v+ v- o e1 v1+ v1- o1 G+ G-)
              (== G '())
              (== `(inc #f) e)
              (== empty-object o)
              (== q (list e v+ v- o))
              (== `(inc ,e1) e)
              (subobjo empty-object o)
              (extend-envo G top-prop G+)
              (extend-envo G bot-prop G-)
              (proveso G+ v+)
              (proveso G- v-)
              (infer G e1 Num v1+ v1- o1)
              (subtypeo Num t)
              ))
  '())

(test "assign bad type to #t, bigger G inlined"
      (run 1 (q)
           (fresh (G e t v+ v- o e1 v1+ v1- o1 G+ G-)
                  (== G `(,(is-prop Num 'arg '())))
                  (== t Num)
                  (extend-envo G bot-prop G+)
                  (extend-envo G top-prop G-)
                  (subtypeo (-val #f) t)
                  (proveso G- v-)
                  (proveso G+ v+)
                  ))
      '())

;TODO
#;(test "assign bad type to #t, bigger G"
  (run 1 (q)
       (fresh (G e t v+ v- o e1 v1+ v1- o1 G+ G-)
              ;(subobjo empty-object o)
              ;(extend-envo G top-prop G+)
              ;(extend-envo G bot-prop G-)
              ;(proveso G+ v+)
              ;(proveso G- v-)
              (infer G #f Num v1+ v1- o1)
              ;(subtypeo Num t)
              ))
  '())

(test "inc of boolean should fail"
  (run 1 (q)
    (infer '() '(inc #t) q top-prop top-prop empty-object))
  '())

(test "local"
  (run 1 (q)
       (fresh (v+ v- o)
              (infer `(,(is-prop Num 'arg '())) 'arg q v+ v- o)))
  '(num))

(test "function type fresh"
  (run 1 (q)
       (fresh (v+ v- o)
              (infer '() '(lambda (arg : num) (inc arg)) q v+ v- o)))
  '((num -> num tt tt empty)))

(test "bad inc"
      (run 1 (q)
           (fresh (v+ v- o)
                  (infer '() '(inc #f) q v+ v- o)))
      '())

(test "bad inc with triv env"
      (run 1 (q)
           (fresh (v+ v- o)
                  (infer `(,top-prop) '(inc #f) q v+ v- o)))
      '())

(test "bad inc with bot env"
      (run 1 (q)
           (fresh (v+ v- o)
                  (infer `(,bot-prop) '(inc #f) q v+ v- o)))
      '())

(test "bad inc with env"
      (run 1 (q)
           (fresh ()
                  (infer `(,(is-prop Num 'x '())) '(inc #f) Num top-prop top-prop empty-object)))
      '())

(test "function type"
  (run 1 (q)
    (infer '() '(lambda (arg : num) (inc arg)) q top-prop top-prop empty-object))
  '((num -> num tt tt empty)))

;; this needs an expected type
(test "bad function type"
  (run 1 (q)
    (infer '() '(lambda (arg : num) (inc #f)) '(num -> num tt tt empty) top-prop top-prop empty-object))
  '())

;; this needs an expected type
(test "should fail when argument used contrary to type declaration"
  (run 1 (q)
    (infer '() '(lambda (arg : (val #f)) (inc arg)) '((val #f) -> num tt tt empty) top-prop top-prop empty-object))
  '())

(test "should fail when one element of arg union type is incompatible with usage"
  (run 1 (q)
    (infer '() '(lambda (arg : (U (val #f) num)) (inc arg)) '((U (val #f) num) -> num tt tt empty) top-prop top-prop empty-object))
  '())

(test "ann propagate expected"
      (run 1 (q)
           (infer '() '(ann 1 num) q top-prop top-prop empty-object))
      '(num))

(test "long ann propagate expected"
      (run 1 (q)
           (infer '() '(ann 1 num tt tt empty) q top-prop top-prop empty-object))
      '(num))

(test "bad ann propagate expected"
      (run 1 (q)
           (infer '() '(ann #f num) q top-prop top-prop empty-object))
      '())

(test "bad long ann propagate expected"
      (run 1 (q)
           (infer '() '(ann 1 num ff ff empty) q top-prop top-prop empty-object))
      '(num))

(test "simple if with lambda, no vars"
  (run 1 (q)
        (infer '() '(lambda (arg : (U (val #f) num))
                      (if arg 0 0))
               '((U (val #f) num) -> num tt tt empty) top-prop top-prop empty-object))
  '(_.0))

(test "simple if with lambda, with vars"
  (run 1 (q)
        (infer '() '(lambda (arg : (U (val #f) num))
                      (if arg arg arg))
               '((U (val #f) num) -> (U (val #f) num) tt tt empty) top-prop top-prop empty-object))
  '(_.0))

; Not implemented yet.
;
; prop-env at if: (arg (U (val #f) num))
; prop-env at (inc arg): ((arg (U (val #f) num))
;                         (arg (not (val #f))))
;
; need to combine information from the two propositions to derive the proposition (arg num).
;
; This will involve writing a function env+ that takes a proposition environment and a proposition
; and returns a new proposition environment with the derived (positive) proposition. This is the proposition
; that the variable case will access.
; the `then` case then becomes
; (fresh ()
;   (env+ prop-env then-prop prop-env^)
;   (infer then prop-env^ t1)
; and similarly for the else branch.
;
(test "should infer correct branch of union from if condition"
  (run 1 (q)
        (infer '() '(lambda (arg : (U (val #f) num))
                      (if arg (ann (inc arg) num) 0))
               '((U (val #f) num) -> num tt tt empty) top-prop top-prop empty-object))
  ; I'm not 100% certain of this expected output.
  '(((U (val #f) num) -> (U num 0))))
