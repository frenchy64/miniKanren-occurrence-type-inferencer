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
            [(== bot-prop a)
             (conde
              [(== bot-prop prop)] ;; helps infer props for conditional tests
              [(== #t #t)])]
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

;; assumes s is a val
(define (val-overlapo s t b)
  (valo s)
  (conde
   [(== s t)
    (== b #t)]
   [(=/= s t)
    (conde
     [(fresh (v1)
             (== (-val v1) s)
             (conde
              [(numbero v1)
               (conde
                [(fresh (v2)
                        (== (-val v2) t)
                        (numbero v2)
                        (=/= v1 v2)
                        (== b #f))]
                [(fresh (v2)
                        (== (-val v2) t)
                        (booleano v2)
                        (== b #f))]
                [(== Bool t)
                 (== b #f)]
                [(not-valo t)
                 (=/= t Bool)
                 (== b #t)])]
              [(booleano v1)
               (conde
                [(fresh (v2)
                        (== (-val v2) t)
                        (booleano v2)
                        (=/= v1 v2)
                        (== b #f))]
                [(fresh (v2)
                        (== (-val v2) t)
                        (numbero v2)
                        (== b #f))]
                [(== Num t)
                 (== b #f)]
                [(not-valo t)
                 (=/= t Num)
                 (== b #t)])]))])]))

(define (valo t)
  (fresh (v1)
         (== (-val v1) t)))

(define (not-valo t)
  (fresh (tag tag2 v1 v2 v3 v4)
         (conde
          [(== `(,tag ,v1) t)
           (=/= tag 'val)]
          [(== `(,tag2 ,v2 ,v3 . ,v4) t)]
          [(symbolo t)])))

(define (bool-and b1 b2 b3)
  (conde
   [(== b1 #f) (== b3 #f)]
   [(== b2 #f) (== b3 #f)]
   [(== b1 #t)
    (== b2 #t)
    (== b3 #t)]))
   
;; conservative
;; TODO unions
(define (overlapo s t b)
  (conde
   [(== s t)
    (== b #t)]
   [(=/= s t)
    (conde
     ;; handle vals
     [(fresh (b1 b2)
         (conde
          [(== b2 #t)
           (val-overlapo t s b1)]
          [(== b1 #t)
           (val-overlapo s t b2)])
         ;; if one of these are false then there is no overlap
         (bool-and b1 b2 b))]
     [(not-valo s)
      (not-valo t)
      (== b #t)])]))

(test "overlap vals number"
      (run 2 (q) (overlapo (-val 1) (-val 1) q))
      '(#t))

(test "bad val-overlapo vals number 1"
      (run 2 (q) (val-overlapo (-val 1) (-val 2) q))
      '(#f))

(test "bad val-overlapo vals number 2"
      (run 2 (q) (val-overlapo (-val 2) (-val 1)  q))
      '(#f))

(test "bad overlap vals number"
      (run 5 (q) (overlapo (-val 1) (-val 2) q))
      '(#f #f))

(test "overlap vals"
      (run 2 (q) (overlapo (-val #f) (-val #f) q))
      '(#t))

(test "bad overlap vals 1"
      (run 5 (q) (overlapo (-val #f) (-val #t) q))
      '(#f #f))

(test "bad overlap vals 2"
      (run 5 (q) (overlapo (-val #t) (-val #f)  q))
      '(#f #f))

(test "val-overlapo #f/Num"
      (run 2 (q)
           (val-overlapo (-val #f) Num q))
      '(#f))

(test "overlapo #f/Num"
      (run 2 (q)
           (overlapo (-val #f) Num q))
      '(#f))
                      
(test "val-overlapo 1/Num"
      (run 2 (q)
           (val-overlapo (-val 1) Num q))
      '(#t))

(test "overlapo 1/Num"
      (run 2 (q)
           (overlapo (-val 1) Num q))
      '(#t))

(test "overlapo Top 1"
      (run 2 (q)
           (overlapo Top Num q))
      '(#t))

(test "overlapo Top 2"
      (run 2 (q)
           (overlapo Num Top q))
      '(#t))

(test "overlapo Bot 1"
      (run 2 (q)
           (overlapo Bot Num q))
      '(#t))

(test "overlapo Bot 2"
      (run 2 (q)
           (overlapo Num Bot q))
      '(#t))

(define (Uno s t r)
  (conde
   [(== s t)
    (== s r)]
   [(=/= s t) ;; this assumption is used below
    (conde
     ;; use Top, helps disambiguate below
     [(conde
       [(== Top s)
        (== Bot t)]
       [(== Bot s)
        (== Top t)])
      (== Top r)]
     ;; use s
     [(conde
       [(== Top s)
        (=/= Bot t)]
       [(== Bot t)
        (=/= Top s)])
      (== s r)]
     ;; use t
     [(conde
       [(== Top t)
        (=/= Bot s)]
       [(== Bot s)
        (=/= Top t)])
      (== t r)]
     [(=/= Top s)  ;; neither are Top
      (=/= Bot s) ;; neither are Bot
      (conde
       [(fresh (l1 r1)
               (=/= l1 t)
               (=/= r1 t)
               (== (Un l1 r1) s)
               (Uno l1 r1 s)
               (== r (Un s t)))]
       [(fresh (l1 r1)
               (=/= l1 s)
               (=/= r1 s)
               (== (Un l1 r1) t)
               (Uno l1 r1 t)
               (== r (Un s t)))]
       [(fresh (l1 l2 r1 r2)
               (overlapo s t #f)
               (== r (Un s t)))]
       [(fresh ()
               (overlapo s t #t)
               (conde
                [(subtypeo s t)
                 (== r t)]
                [(subtypeo t s)
                 (== r s)]))])])]))

; Succeed if child-type is a subtype of parent-type,
; like (var #f) is a subtype of Bool.
(define (subtypeo child-type parent-type)
  (conde
   ;; going first helps inference
   [(== child-type parent-type)
    (=/= Bot child-type)
    (=/= Top child-type)]
   [(== Bot child-type)
    (== Top parent-type)]
   [(== Bot child-type)
    (=/= Top parent-type)]
   [(=/= Bot child-type)
    (== Top parent-type)]
   [(=/= Bot child-type)
    (=/= Top parent-type)
    (conde
     [(=/= child-type parent-type)
      (conde
       [(fresh (t1 t2)
               ;; must be the shape of a union but with the
               ;; same rules as Uno
               (== (Un t1 t2) child-type)
               (Uno t1 t2 child-type)
               (subtypeo t1 parent-type)
               (subtypeo t2 parent-type))]
       [(fresh (t1 t2)
               ;; must be the shape of a union but with the
               ;; same rules as Uno
               (== (Un t1 t2) parent-type)
               (Uno t1 t2 parent-type)
               (conde
                [(subtypeo child-type t1)]
                [(subtypeo child-type t2)]))]
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
               (proveso `(,v1+) v2+)
               (proveso `(,v1-) v2-)
               (subtypeo arg2 arg1)
               (subtypeo ret1 ret2))])])]))
     
(test "Uno Top"
      (run 2 (q)
           (Uno Top Top q))
      `(,Top))

(test "Uno Bot"
      (run 2 (q)
           (Uno Bot Bot q))
      `(,Bot))


(test "Uno Bot and Top 1"
      (run 2 (q)
           (Uno Top Bot q))
      `(,Top))

(test "Uno Bot and Top 2"
      (run 2 (q)
           (Uno Bot Top q))
      `(,Top))

(test "Uno val#f/Num"
      (run 2 (q)
           (Uno (-val #f) Num q))
      `(,(Un (-val #f) Num)))

(test "Uno Num/val#f"
      (run 2 (q)
           (Uno Num (-val #f)  q))
      `(,(Un Num (-val #f))))

(test "Uno overlap 1"
      (run 3 (q)
           (Uno (-val 1) Num q))
      `(,Num))

(test "Uno overlap 1"
      (run 3 (q)
           (Uno Num (-val 1) q))
      `(,Num))

(test "subtype reflexive"
      (run 2 (q)
           (subtypeo Num Num))
      '(_.0))

(test "subtype reflexive"
      (run 2 (q)
           (subtypeo Bool Bool))
      '(_.0))


(test "subtype function"
      (run 2 (q)
           (subtypeo q `(Num -> Num tt tt empty)))
      '((Num -> Num tt tt empty) Nothing))

(test "subtype function contra expanded"
      (run 2 (q)
           (subtypeo Num Num)
           (subtypeo (-val 1) Num)
           
           #;(subtypeo '(Num -> Num tt tt empty) '((val 1) -> Num tt tt empty)))
      '(_.0))

(test "subtype function contra"
      (run 2 (q)
           (subtypeo '(Num -> Num tt tt empty) '((val 1) -> Num tt tt empty)))
      '(_.0))

(test "bad subtype function contra"
      (run 1 (q)
           (subtypeo '(Num -> Num tt tt empty) '((val #f) -> Num tt tt empty)))
      '())

(test "subtype function rng"
      (run 1 (q)
           (subtypeo '(Num -> (val 1) tt tt empty) '(Num -> Num tt tt empty)))
      '(_.0))

(test "bad subtype val"
      (run 1 (q)
           (subtypeo (-val #f) (-val #t)))
      '())

(test "bad subtype val #f/Num"
      (run 1 (q)
           (subtypeo (-val #f) Num))
      '())

(test "bad subtype Bot"
      (run 1 (q)
           (subtypeo (-val #f) Bot))
      '())

(test "Bot one supertype"
      (run 2 (q)
           (subtypeo Bot Num))
      '(_.0))

(test "Bot exactly 2 supertypes"
      (run 3 (q)
           (subtypeo Bot q))
      '(Any (_.0 (=/= ((_.0 Any))))))

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
    [(fresh (e1 e2 e3 tb2 tb3 G2 G3
             t1 v1+ v1- v2+ v2- v3+ v3- o1 o2 o3)
       (== `(if ,e1 ,e2 ,e3) e)
       
       (infer G e1 t1 v1+ v1- o1)
       (extend-envo G v1+ G2)
       (extend-envo G v1- G3)
       (infer G2 e2 tb2 v2+ v2- o2)
       (infer G3 e3 tb3 v3+ v3- o3)
       
       (fresh (tact v+act v-act oact)
              (conde
               ;; both branches unreachable
               [(membero G2 bot-prop)
                (membero G3 bot-prop)
                (== bot-prop v+act)
                (== bot-prop v-act)
                ;; and, object is unrestrained
                (== Bot tact)]
               ;; unreachable then branch, use else branch type/props/object
               [(membero G2 bot-prop)
                (not-membero G3 bot-prop)
                (== tb3 tact)
                (== v3+ v+act)
                (== v3- v-act)
                (== o3 oact)]
               ;; unreachable else branch, use then branch type/props/object
               [(not-membero G2 bot-prop)
                (membero G3 bot-prop)
                (== tb2 tact)
                (== v2+ v+act)
                (== v2- v-act)
                (== o2 oact)]
               ;; both branches reachable
               [(not-membero G2 bot-prop)
                (not-membero G3 bot-prop)
                (Uno tb2 tb3 tact)
                (oro v2+ v3+ v+act)
                (oro v2- v3- v-act)
                (common-objo o2 o3 oact)])
              
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
      (run 2 (q)
           (subtypeo (-val #t) q)
           )
      '((val #t) Any))

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
      (run 2 (q)
           (subobjo empty-object q))
      '(empty))

(test "bad subobjo"
      (run 3 (q)
           (subobjo 'x q))
      '(x empty))

(test "common-objecto empty"
      (run 2 (q)
           (common-objo empty-object empty-object q))
      '(empty))

(test "common-objecto x"
      (run 2 (q)
           (common-objo 'x 'x q))
      '(x))

(test "common-objecto to empty left"
      (run 2 (q)
           (common-objo empty-object 'x q))
      `(,empty-object))

(test "common-objecto to empty right"
      (run 2 (q)
           (common-objo 'x empty-object q))
      `(,empty-object))

(test "plain #t, fresh props and o"
      (run 3 (q)
           (fresh (v+ v- o)
                  (infer '() #t q v+ v- o)))
      '((val #t) (val #t) Any ))

(test "plain #t, fresh v- and o"
      (run 3 (q)
           (fresh (v+ v- o)
                  (infer '() #t q top-prop v- o)))
      '((val #t) (val #t) Any))

(test "plain #t, fresh o"
      (run 3 (q)
           (fresh (v+ v- o)
                  (infer '() #t q top-prop top-prop o)))
      '((val #t) Any (val #t)))

(test "plain #t, fresh o, accurate props"
      (run 3 (q)
           (fresh (v+ v- o)
                  (infer '() #t q top-prop bot-prop o)))
      '((val #t) (val #t) Any))

(test "plain #t"
  (run 3 (q)
    (infer '() #t q top-prop bot-prop empty-object))
  '((val #t) (val #t) Any))

(test "good plain #f accurate props"
  (run 3 (q)
    (infer '() #f q bot-prop top-prop empty-object))
  '((val #f) (val #f) Any))

(test "good plain #f, top-props"
  (run 3 (q)
    (infer '() #f q top-prop top-prop empty-object))
  '((val #f)  Any (val #f)))


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
  (run 3 (q)
    (fresh (v+ v- o)
           (infer '() '(if #t #t #t) q v+ v- o)))
  '((val #t) (val #t) Any))

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

(test "bad transitive subtype"
      (run 1 (q)
           (subtypeo (-val #f) q)
           (subtypeo q Num))
      '())

(test "simulate bad if, unreachable else branch with fresh type/props/object"
      (run 1 (q)
           (fresh (G t v+ v- o)
                  (== G `())
                  (subtypeo (-val #f) q)
                  (subtypeo q Num)
                  #;(check-belowo G
                                t   v+       v-       o
                                Bot top-prop top-prop empty-object)))
      '())

(test "proveso top-prop should only return one answer"
      (run* (q)
           (fresh (v+ v- o)
                  (proveso `(,top-prop) q)))
      '(tt))

(test "proveso infer bot-prop"
      (run 3 (q)
           (proveso `(,bot-prop) q))
      `(,bot-prop _.0))

;TODO
#;(test "if, unreachable else branch bad type"
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

(test "number literal inference"
      (run 3 (q)
           (fresh (t v+ v- o)
                  (== q `(,t ,v+ ,v- ,o))
                  (infer '() 1 t v+ v- o)))
      '(((val 1) tt ff empty) ((val 1) tt _.0 empty) (Any tt ff empty)))

(test "true literal inference"
      (run 3 (q)
       (fresh (t v+ v- o)
              (== q `(,t ,v+ ,v- ,o))
              (infer '() #t t v+ v- o)))
      '(((val #t) tt ff empty) ((val #t) tt _.0 empty) (Any tt ff empty)))

(test "false literal inference"
      (run 3 (q)
           (fresh (t v+ v- o)
                  (== q `(,t ,v+ ,v- ,o))
                  (infer '() #f t v+ v- o)))
      '(((val #f) ff tt empty) ((val #f) _.0 tt empty) (Any ff tt empty)))

(test "inc inference"
      (run 3 (q)
       (fresh (t v+ v- o)
              (== q `(,t ,v+ ,v- ,o))
              (infer '() '(inc 1) t v+ v- o)))
      '((Num tt ff empty) (Num tt _.0 empty) (Any tt ff empty)))

(test "if then branch only type"
      (run 2 (q)
           (infer '() '(if #f #f #f) (-val #t) top-prop top-prop empty-object))
      '())

(test "no way to construct object"
      (run 100 (q)
           (fresh (v+ v- o)
                  (infer '() q Top top-prop top-prop 'x)))
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
