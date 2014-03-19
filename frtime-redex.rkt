#lang racket (require redex rackunit)

(define-language FrTime
  ;; Store locations
  ;; TODO: is this right?
  (σ (loc x) (loc ⊥))

  ;; Variables
  (x variable-not-otherwise-mentioned)
  ;; Primatives
  (p + - * / < >)
  ;; Values
  ((u v)
   ⊥ true false n p (lambda (x ...) e) σ)
  ;; Numbers
  (n number)
  ;; Expressions
  (e v x (e e ...) (delay e n) (if e e e))

  ;; Contexts
  (E hole (v ... E e ...) (delay E n) (if E e e))

  ;; Signal Types
  (s (lift p v ...)
     (delay σ n σ)
     (dyn (lambda (x) e) σ σ)
     (fwd σ)
     input
     const))

(module+ test
  (define no-signals
    (term (if (> (+ 3 8) (- 9 2))
              ((lambda (a b) (- b a)) 4 5)
              true)))
  (define lifted-+
    (term (+ 3 (loc var0))))
  (define signal-in-if
    (term ((lambda (n) (if (< n (+ n 5)) true false)) (loc seconds))))

  (test-equal (redex-match? FrTime e no-signals) #t)
  (test-equal (redex-match? FrTime e lifted-+) #t)
  (test-equal (redex-match? FrTime e signal-in-if) #t))

;; Blatently stolen from http://www.ccs.neu.edu/home/matthias/7400-s14/subst.rkt
;; Thanks!!
(define-metafunction FrTime
  subst-n : (x any) ... any -> any
  [(subst-n (x_1 any_1) (x_2 any_2) ... any_3)
   (subst x_1 any_1 (subst-n (x_2 any_2) ... any_3))]
  [(subst-n any_3)
   any_3])

;; (subst x e_1 e) replaces all occurrences of
;; x in e with e_1 HYGIENICALLY
(define-metafunction FrTime
  subst : x any any -> any
  ;; 1. x_1 bound, so don't continue in λ body
  [(subst x_1 any_1 (lambda (x_2 ... x_1 x_3 ...) any_2))
   (lambda (x_2 ... x_1 x_3 ...) any_2)]
  ;; 2. general purpose capture avoiding case
  [(subst x_1 any_1 (lambda (x_2 ...) any_2))
   (lambda (x ...) (subst x_1 any_1 (subst-vars* (x_2 x) ... any_2)))
   (where (x ...) ,(variables-not-in (term (x_1 any_1 any_2)) (term (x_2 ...))))]
  ;; 3. replace x_1 with e_1
  [(subst x_1 any_1 x_1) any_1]
  ;; 4. x_1 and x_2 are different, so don't replace
  [(subst x_1 any_1 x_2) x_2]
  ;; the last two cases cover all other expression forms
  [(subst x_1 any_1 (any_2 ...))
   ((subst x_1 any_1 any_2) ...)]
  [(subst x_1 any_1 any_2) any_2])

;; (subst-vars (x_1 e_1) ... e) replaces all occurrences of
;; x_1, ... in e with e_1, ... UNCONDITIONALLY
(define-metafunction FrTime
  subst-vars* : (x any) ... any -> any
  [(subst-vars* any)
   any]
  [(subst-vars* (x_1 any_1) (x_2 any_2) ... any)
   (subst-vars x_1 any_1 (subst-vars* (x_2 any_2) ... any))])

;; (subst-vars x e_1 e) replaces all occurrences of
;; x in e with e_1 UNCONDITIONALLY
(define-metafunction FrTime
  subst-vars : x any any -> any
  [(subst-vars x_1 any_1 x_1) any_1]
  [(subst-vars x_1 any_1 (any_2 ...)) ((subst-vars x_1 any_1 any_2) ...)]
  [(subst-vars x_1 any_1 any_2) any_2]
  [(subst-vars x_1 any_1 (x_2 any_2) ... any_3)
   (subst-vars x_1 any_1 (subst-vars ((x_2 any_2) ... any_3)))])

(define-extended-language FrTime-Semantics FrTime
  (Σ ::=
     (σ ...))
  (I ::=
     (i ...))
  (i ::=
     σ
     (σ v))
  (X ::=
     (xs ...))
  (xs ::=
      (σ v n))
  (S ::=
     ((v -> sis) ...))
  (sis ::=
       (v s (σ ...)))
  (t ::=
     n))

(module+ test
  (define S1
    (term (((loc var0) -> (4 (lift + 3 (loc var4)) ()))
           ((loc var4) -> (2 const ((loc var0)))))))
  (define S2
    (term (((loc var4) -> (⊥ const ()))
           ((loc var2) -> (94 const ((loc var80))))
           ((loc var3) -> (20 input ((loc var20)))))))
  (define S3
    (term (((loc var4) -> (⊥ const ((loc var9))))
           ((loc var2) -> (94 const ((loc var9) (loc var80))))
           ((loc var3) -> (20 input ((loc var20)))))))
  (define Σ1 (term ((loc var0) (loc var3) (loc var9))))

  (test-equal (redex-match? FrTime-Semantics S S1) #t)
  (test-equal (redex-match? FrTime-Semantics S S2) #t)
  (test-equal (redex-match? FrTime-Semantics S S3) #t)
  (test-equal (redex-match? FrTime-Semantics Σ Σ1) #t))

;; δ : p v ... -> v
;; Primitive application.
(define-metafunction FrTime
  δ : p v ... -> v
  [(δ + n ...) ,(apply + (term (n ...)))]
  [(δ - n ...) ,(apply - (term (n ...)))]
  [(δ * n ...) ,(apply * (term (n ...)))]
  [(δ / n ...) ,(apply / (term (n ...)))]
  [(δ < n ...) ,(if (apply < (term (n ...))) (term true) (term false))]
  [(δ > n ...) ,(if (apply > (term (n ...))) (term true) (term false))]
  [(δ p v ...) 
   ,(error "primitive application not supported!" 
	   (term p)
	   (term (v ...)))])

(module+ test
  (test-equal (term (δ + 3 4)) (term 7))
  (test-exn
   "Errors on bad values"
   (lambda (x) #t)
   (lambda () (term (δ + (lambda (x) x) 9)))))

;; get-signal-in-store : S v -> sis or #f
;; Returns the information in the signal store for given signal v, or
;; #f is no such signal is found
(define-metafunction FrTime-Semantics
  get-signal-in-store : S v -> sis or #f
  [(get-signal-in-store ((v_1 -> sis_1) ... (v -> sis) (v_2 -> sis_2) ...) v)
   sis
   (side-condition (not (member (term v) (term (v_1 ...)))))]
  [(get-signal-in-store S v) #f])

(module+ test
  (test-equal (term (get-signal-in-store ,S1 (loc var4)))
              (term (2 const ((loc var0)))))
  (test-equal (term (get-signal-in-store ,S1 (loc var99)))
              (term #f)))

;; get-signal-in-store : S v sis -> S
;; Updates or adds the signal v in the given store with the given
;; value, returning the updated store
(define-metafunction FrTime-Semantics
  set-signal-in-store : S v sis -> S
  [(set-signal-in-store ((v_1 -> sis_1) ... (v -> sis_old) (v_2 -> sis_2) ...) v sis)
   ((v_1 -> sis_1) ... (v -> sis) (v_2 -> sis_2) ...)
   (side-condition (not (member (term v) (term (v_1 ...)))))]
  [(set-signal-in-store ((v_1 -> sis_1) ...) v sis)
   ((v -> sis) (v_1 -> sis_1) ...)])

(module+ test
  (test-equal (term (set-signal-in-store ,S1 (loc var0) (309 const ())))
              (term (((loc var0) -> (309 const ()))
                     ((loc var4) -> (2 const ((loc var0)))))))
  (test-equal (term (set-signal-in-store ,S1 (loc var9) (309 const ())))
              (term (((loc var9) -> (309 const ()))
                     ((loc var0) -> (4 (lift + 3 (loc var4)) ()))
                     ((loc var4) -> (2 const ((loc var0))))))))

;; Vs : S v -> v
;; Get the current value of the given sigma
(define-metafunction FrTime-Semantics
  Vs : S v -> v
  [(Vs S σ) v_2
   (where (v_2 s_any Σ_any) (get-signal-in-store S σ))]
  [(Vs S v) v])

(module+ test
  (test-equal (term (Vs ,S1 (loc var0))) 4)
  (test-equal (term (Vs ,S1 (loc var4))) 2))

;; A : Σ v v -> Σ
;; Returns Sigma if the values are equal, or the empty list
;; otherwise
(define-metafunction FrTime-Semantics
  A : Σ v v -> Σ
  [(A Σ v v) Σ]
  [(A Σ v v_other) ()])

(module+ test
  (test-equal (term (A ,Σ1 (lambda (x) x) (lambda (x) x))) Σ1)
  (test-equal (term (A ,Σ1 (lambda (x) x) (loc var5))) (term ())))

;; reg : σ Σ S -> S
;; Registers the given signal location with each location in Σ in S
(define-metafunction FrTime-Semantics
  reg : σ Σ S -> S
  [(reg σ () S) S]
  [(reg σ (σ_prime σ_prime2 ...) S)
   (reg σ (σ_prime2 ...) S_updated)
   (where (v s (σ_primeset ...)) (get-signal-in-store S σ_prime))
   (where S_updated (set-signal-in-store S σ_prime (v s (σ σ_primeset ...))))])

(module+ test
  (test-equal (term (reg (loc var9) ((loc var4) (loc var2)) ,S2)) S3))

;; Ds : S Σ -> Σ
;; Returns the set of the union of all dependencies for each σ ∈ Σ
(define-metafunction FrTime-Semantics
  Ds : S Σ -> Σ
  [(Ds S Σ) (Ds* S Σ ())])

(module+ test
  (test-equal (term (Ds ,S2 ((loc var9)))) (term ()))
  (test-equal (term (Ds ,S2 ((loc var2) (loc var3)))) (term ((loc var20) (loc var80)))))

;; Helper function for Ds. Accummulates values in the second sigma and
;; setifies them once they're all collected.
(define-metafunction FrTime-Semantics
  Ds* : S Σ Σ -> Σ
  [(Ds* S () Σ) ,(remove-duplicates (term Σ))]
  [(Ds* S (σ_first σ_rest ...) (σ_acc ...))
   (Ds* S (σ_rest ...) (σ_first-in-store ... σ_acc ...))
   (where (v_any s_any (σ_first-in-store ...)) (get-signal-in-store S σ_first))]
  [(Ds* S (σ_first σ_rest ...) Σ) (Ds* S (σ_rest ...) Σ)])

;; dfrd : S I -> Σ
;; Returns the set of all signal locations that are transitively
;; dependant on the signal locations in I
(define-metafunction FrTime-Semantics
  dfrd : S I -> Σ
  [(dfrd S I) (dfrd* S (Ds S (I->Σ I ())))])

;; dfrd* : S Σ -> Σ
;; Helper method for dfrd
(define-metafunction FrTime-Semantics
  dfrd* : S Σ -> Σ
  [(dfrd* S (σ ...) ())
   (dfrd* S Σ)
   (where (σ_Ds ...) (Ds S (σ ...)))
   (where Σ ,(remove-duplicates (term (σ ... σ_Ds ...))))
   (side-condition (not (equal? (term (σ ...)) (term Σ))))]
  [(dfrd* S Σ) Σ])

(module+ test
  (define Sdfrd
    (term
     (((loc var0) -> (1 const ()))
      ((loc var1) -> (1 const ((loc var0) (loc var2))))
      ((loc var2) -> (2 const ((loc var3))))
      ((loc var3) -> (3 const ()))
      ((loc var4) -> (4 const ())))))

  (test-equal
   (term (dfrd ,Sdfrd ((loc var1) (loc var2))))
   (term ((loc var0) (loc var2) (loc var3))))  
  #;
  (test-equal
   (term (dfrd* ,Sdfrd ((loc var1))))
   (term ((loc var1) (loc var0) (loc var2) (loc var3)))))

;; I->Σ : I Σ -> Σ
;; Get all of the signal locations out of a set of internal events.
(define-metafunction FrTime-Semantics
  I->Σ : I Σ -> Σ
  [(I->Σ () Σ) Σ]
  [(I->Σ (σ_first i ...) (σ_acc ...))
   (I->Σ (i ...) (σ_first σ_acc ...))]
  [(I->Σ ((σ_first v) i ...) (σ_acc ...))
   (I->Σ (i ...) (σ_first σ_acc ...))])

(module+ test
  (test-equal
   (term (I->Σ (((loc var9) 3) (loc var10) ((loc var4) 1)) ()))
   (term ((loc var4) (loc var10) (loc var9)))))

;; remove-all : (any ...) (any ...) -> (any ...)
;; Removes all of the elements of the second list from the first.
(define-metafunction FrTime-Semantics
  remove-all : (any ...) (any ...) -> (any ...)
  [(remove-all (any ...) ()) (any ...)]
  [(remove-all (any_begin ... any any_end ...) (any any_rest ...))
   (remove-all (any_begin ... any_end ...) (any any_rest ...))]
  [(remove-all (any ...) (any_rem any_rest ...))
   (remove-all (any ...) (any_rest ...))
   (side-condition (not (member (term any_rem) (term (any ...)))))])

(module+ test
  (test-equal
   (term (remove-all (1 2 4 5 4 5) (1 4)))
   (term (2 5 5)))
  (test-equal (term (remove-all (1 2 3 4 5) (6)))
              (term (1 2 3 4 5))))

;; del : Remove locations from the given Σ from the dependency tree.
;; Maintain state of the graph in other places to accommodate for deletion,
;; and make sure to keep track of dynamic dependencies that can't be deleted yet
(define-metafunction FrTime-Semantics
  del : S Σ -> (S Σ)
  [(del S Σ) (del-accum S Σ () ())])

(define-metafunction FrTime-Semantics
  del* : S Σ -> (S Σ)
  [(del* S ()) (S ())]
  [(del* S Σ) (del* S_1 Σ_1)
   (where (S_1 Σ_1) (del S Σ))])

(define-metafunction FrTime-Semantics
  del-accum : S Σ S Σ -> (S Σ)
  [(del-accum () Σ_in S_acc Σ_acc) (S_acc Σ_acc)]
  [(del-accum S_in Σ_in S_acc (σ_acc ...))
   (del-accum ((v_rest -> sis_rest) ...) Σ_in S_stored Σ_newacc)
   (where ((v_1 -> sis_1) (v_rest -> sis_rest) ...) S_in)
   (where S_stored (set-signal-in-store S_acc v_1 (del-sis sis_1 Σ_in)))
   (where Σ_newacc (get-dyn-deps sis_1 (σ_acc ...)))])

(module+ test
  (let ([example-S (term (((loc my-x) -> (true const ((loc my-y))))))]
        [example-Σ (term ((loc my-y)))]
        [result-S  (term (((loc my-x) -> (true const ()))))]
        [result-Σ  (term ())])
    (test-equal (term (del* ,example-S ,example-Σ))
                (term (,result-S ,result-Σ))))
  (let ([example-S (term (((loc my-x) ->
                           (true
                            (dyn (lambda (x) x)
                                 (loc my-a)
                                 (loc my-b))
                            ((loc my-y))))))]
        [example-Σ (term ((loc my-y)))]
        [result-S  (term (((loc my-x) ->
                           (true
                            (dyn (lambda (x) x)
                                 (loc my-a)
                                 (loc my-b))
                            ()))))]
        [result-Σ  (term ((loc my-y)))])
    (test-equal (term (del ,example-S ,example-Σ))
                (term (,result-S ,result-Σ)))))

;; get-dyn-deps : When deleting dependencies, we want to retain the 
;; dependencies from dynamic signals in the accumulator, and
;; ignore depenencies from other signals.
(define-metafunction FrTime-Semantics
  get-dyn-deps : sis Σ -> Σ
  [(get-dyn-deps (v (dyn (lambda (x) e) σ_1 σ_2) (σ_dyn ...)) (σ_acc ...))
   ,(remove-duplicates (term (σ_dyn ... σ_acc ...)))]
  [(get-dyn-deps (v s Σ_sis) Σ_acc) Σ_acc])

(module+ test
  (test-equal (term (get-dyn-deps (true
                                   (dyn (lambda (x) (+ x 3))
                                        (loc my-a)
                                        (loc my-b))
                                   ((loc my-z)))
                                  ()))
              (term ((loc my-z))))
  (test-equal (term (get-dyn-deps (true const ((loc my-z))) ()))
              (term ())))

;; del-sis : easier way to abstract a call to remove-all (from within del).
;; Eliminates the given Σ from the dependency list of the given SIS
(define-metafunction FrTime-Semantics
  del-sis : sis Σ -> sis
  [(del-sis (v s Σ) Σ_rem) (v s (remove-all Σ Σ_rem))])

(module+ test
  (test-equal (term (del-sis (3 const ((loc my-x) (loc my-y) (loc my-z)))
                             ((loc my-y)  (loc my-z))))
              (term (3 const ((loc my-x)))))
  (test-equal (term (del-sis (true const ()) ((loc my-z) (loc my-abc))))
              (term (true const ()))))

;; externals-at-time : Search through the external signal list X,
;; pull out signals that triggered at the given t value
(define-metafunction
  FrTime-Semantics
  externals-at-time : X n -> I
  [(externals-at-time X n) (externals-at-time* X n ())])

(define-metafunction FrTime-Semantics
  externals-at-time* : X n I -> I
  [(externals-at-time* () n_time I) I]
  [(externals-at-time* ((σ_1 v_1 n_time) (σ_rest v_rest n_rest) ...) n_time (i ...))
   (externals-at-time* ((σ_rest v_rest n_rest) ...) n_time ((σ_1 v_1) i ...))]
  [(externals-at-time* ((σ_1 v_1 n_1) (σ_rest v_rest n_rest) ...) n_time I)
   (externals-at-time* ((σ_rest v_rest n_rest) ...) n_time I)])

(module+ test
  (let ([simple-x (term (((loc my-a) true 5)
                         ((loc my-b) false 7)
                         ((loc my-c) (lambda (x) x) 5)
                         ((loc my-d) + 7)
                         ((loc my-e) ⊥ 6)))]
        [i-at-seven (term (((loc my-d) +) ((loc my-b) false)))]
        [i-at-five  (term (((loc my-c) (lambda (x) x)) ((loc my-a) true)))])
    (test-equal (term (externals-at-time ,simple-x 5))
                i-at-five)
    (test-equal (term (externals-at-time ,simple-x 7))
                i-at-seven)))

(define-metafunction FrTime-Semantics
  signalify : (S I v) x -> (S I σ)
  [(signalify (S I σ) x) (S I σ)]
  [(signalify (S I v) x) (S_prime I σ)
   (where σ (loc x))
   (where S_prime (set-signal-in-store S σ (v const ())))])

(define-metafunction FrTime-Semantics
  dom : S -> Σ
  [(dom ((σ -> sis) ...)) (σ ...)])

(define ->construction
  (reduction-relation
   FrTime-Semantics
   #:domain (S I e)
   (--> (S I (in-hole E (p v ...)))
        ;; reduces to
        (S I (in-hole E v_applied))
        (side-condition (andmap (lambda (x) (not (redex-match? FrTime σ x)))
                                (term (v ...))))
        (where v_applied (δ p v ...))
        "primitive-application")
   (--> (S (i ...) (in-hole E (p v ...)))
        ;; reduces to
        (S_prime (σ i ...) (in-hole E σ))
        (where (σ_arg ...)
               ,(filter (lambda (x) (redex-match? FrTime σ x))
                        (term (v ...))))
        (side-condition (not (empty? (term σ_args))))
        (fresh lifted-prim)
        (where x_generated lifted-prim)
        (where σ (loc x_generated))
        (where S_prime
               (reg σ
                    (σ_arg ...)
                    (set-signal-in-store S σ (⊥ (lift p v ...) ()))))
        "primitive-lift")
   (--> (S I (in-hole E ((lambda (x ..._n) e) v ..._n)))
        ;; reduces to
        (S I (in-hole E (subst-n (x v) ... e)))
        "beta-v")
   (--> (S (i ...) (in-hole E (σ v ...)))
        ;; reduces to
        ((reg σ_1 (σ) S_prime)
         (σ_1 i ...)
         (in-hole E σ_2))
        (fresh beta-dyn beta-fwd)
        (where x_beta-dyn beta-dyn)
        (where x_beta-fwd beta-fwd)
        (where σ_1 (loc x_beta-dyn))
        (where σ_2 (loc x_beta-fwd))
        (where S_halfprime
               (set-signal-in-store S
                                    σ_2
                                    (⊥ (fwd (loc ⊥)) ())))
        (where S_prime
               (set-signal-in-store S_halfprime
                                    σ_1
                                    (⊥
                                     (dyn (lambda (x) (x v ...))
                                          σ
                                          σ_2)
                                     ())))
        "beta-v-lift")
   (--> (S I (in-hole E (if true e_1 e_2)))
        ;; reduces to
        (S I (in-hole E e_1))
        "if-true")
   (--> (S I (in-hole E (if false e_1 e_2)))
        ;; reduces to
        (S I (in-hole E e_2))
        "if-false")
   (--> (S (i ...) (in-hole E (if σ e_1 e_2)))
        ;; reduces to
        ((reg σ_1 (σ) S_prime) (σ_1 i ...) (in-hole E σ_2))
        (fresh if-dyn if-fwd)
        (where x_if-dyn if-dyn)
        (where x_if-fwd if-fwd)
        (where σ_1 (loc x_if-dyn))
        (where σ_2 (loc x_if-fwd))
        (where s_dyn-term
               (dyn (lambda (x) (if x e_1 e_2)) σ σ_2))
        (where S_halfprime
               (set-signal-in-store S σ_2 (⊥ (fwd (loc ⊥)) ())))
        (where S_prime
               (set-signal-in-store S_halfprime σ_1 (⊥ s_dyn-term ())))
        "if-lift")
   (--> (S (i ...) (in-hole E (delay σ n)))
        ;; reduces to
        (S_prime (σ_2 i ...) (in-hole E σ_1))
        (fresh delay-input delay-delay)
        (where x_delay-input delay-input)
        (where x_delay-delay delay-delay)
        (where σ_1 (loc x_delay-input))
        (where σ_2 (loc x_delay-delay))
        (where S_halfprime
               (set-signal-in-store S σ_2 (⊥ (delay σ n σ_1) ())))
        (where S_almostprime
               (set-signal-in-store S_halfprime σ_1 (⊥ input ())))
        (where S_prime (reg σ_2 (σ) S_almostprime))
        "delay")))

(define ->update
  (reduction-relation
   FrTime-Semantics
   #:domain (X S I t)
   (--> (X S () t)
        ;; reduces to
        (X S I_prime ,(+ (term t) 1))
        (where I_prime (externals-at-time X ,(+ (term t) 1)))
        "u-shift")
   (--> (X S (i_fst ... σ i_rst ...) t)
        ;; reduces to
        (X S_prime I_prime t)
        (where (v_0 (fwd σ_prime) Σ) (get-signal-in-store S σ))
        (where (v s_any Σ_any) (get-signal-in-store S σ_prime))
        (where S_prime (set-signal-in-store S σ (v (fwd σ_prime) Σ)))
        (where (σ_a ...) (A Σ v_0 v))
        (where I_prime (σ_a ... i_fst ... i_rst ...))
        "u-fwd")
   (--> (X S I t)
        ;; reduces to
        (X S_1 I_prime-cleaned t)
        (where (i_fst ... σ i_rst ...) I)
        (where (⊥ (dyn u σ_1 σ_2) Σ) (get-signal-in-store S σ))
        (where (v (fwd σ_any) Σ_2) (get-signal-in-store S σ_2))
        (where (S_* ()) (del* S Σ))
	(fresh new-const)
	(where x_new-const new-const)
        (where (S_prime I_prime σ_3)
               (signalify 
		,(first
		  (apply-reduction-relation* ->construction (term (S_* I (u (Vs S σ_1))))))
		x_new-const))
        (where S_updated-fwd (set-signal-in-store S_prime σ_2 (v (fwd σ_3) Σ_2)))
        (where S_updated-dyn (set-signal-in-store S_updated-fwd σ (⊥ (dyn u σ_1 σ_2) Σ_prime)))
        (where S_1 (reg σ_2 (σ_3) S_updated-dyn))
        (where I_prime-cleaned (remove-all (remove-all I Σ) (σ)))
        "u-dyn")
   (--> (X S I t)
        ;; reduces to
        (X S_prime I_prime t)
        (where (i_fst ... (σ v) i_rst ...) I)
        (where (v_0 input Σ) (get-signal-in-store S σ))
        (where (σ_a ...) (A Σ v_0 v))
        (where I_prime (σ_a ... i_fst ... i_rst ...))
        (where S_prime (set-signal-in-store σ (v input Σ)))
        "u-input")
   (--> ((xs ...) S (i_fst ... σ i_rst ...) t)
        ;; reduces to
        (X_prime S I_prime t)
        (where (⊥ (delay σ n σ_1) Σ) (get-signal-in-store S σ))
        (where X_prime ((σ_1 (Vs S σ) ,(+ (term t) (term n))) xs ...))
        (where I_prime (i_fst ... i_rst ...))
        "u-delay")
   (--> (X S I t)
        ;; reduces to
        (X S_prime I_prime t)
        (where (i_fst ... σ i_rst ...) I)
        (side-condition (not (member (term σ) (term (dfrd S I)))))
        (where (v_0 (lift p v_1 ...) Σ) (get-signal-in-store S σ))
        (where v (δ p (Vs S v_1) ...))
        (where S_prime (set-signal-in-store S σ (v (lift p v_1 ...) Σ)))
        (where (σ_a ...) (A Σ v_0 v))
        (where I_prime (σ_a ... i_fst ... i_rst ...))
        "u-lift")))

(define signal-in-if
  (term ((lambda (n) (if (< n (+ n 5)) true false)) (loc seconds))))

(define (make-initial-context t)
  (term ((((loc seconds) -> (0 input ()))
	  ((loc key) -> (⊥ input ())))
	 ()
	 ,t)))

#;
(apply-reduction-relation*
 ->construction
 (make-initial-context signal-in-if))

(define if-stmt-term
  (term (()
	 (((loc if-dyn) -> (⊥ (dyn (lambda (x) (if x true false)) (loc lifted-prim1) (loc if-fwd)) ()))
	  ((loc if-fwd) -> (⊥ (fwd (loc ⊥)) ()))
	  ((loc lifted-prim1) -> (⊥ (lift < (loc seconds) (loc lifted-prim)) ((loc if-dyn))))
	  ((loc lifted-prim) -> (⊥ (lift + (loc seconds) 5) ((loc lifted-prim1))))
	  ((loc seconds) -> (0 input ((loc lifted-prim1) (loc lifted-prim))))
	  ((loc key) -> (⊥ input ())))
	 ((loc if-dyn) (loc lifted-prim1) (loc lifted-prim))
	 0)))

(define if-stmt-term-dyn
  (term (()
	 (((loc if-dyn) -> (⊥ (dyn (lambda (x) (if x true false)) (loc lifted-prim1) (loc if-fwd)) ()))
	  ((loc if-fwd) -> (⊥ (fwd (loc ⊥)) ()))
	  ((loc lifted-prim1) -> (⊥ (lift < (loc seconds) (loc lifted-prim)) ((loc if-dyn))))
	  ((loc lifted-prim) -> (⊥ (lift + (loc seconds) 5) ((loc lifted-prim1))))
	  ((loc seconds) -> (0 input ((loc lifted-prim1) (loc lifted-prim))))
	  ((loc key) -> (⊥ input ())))
	 ((loc if-dyn))
	 0)))

(define if-stmt-term-prim1
  (term (()
	 (((loc if-dyn) -> (⊥ (dyn (lambda (x) (if x true false)) (loc lifted-prim1) (loc if-fwd)) ()))
	  ((loc if-fwd) -> (⊥ (fwd (loc ⊥)) ()))
	  ((loc lifted-prim1) -> (⊥ (lift < (loc seconds) (loc lifted-prim)) ((loc if-dyn))))
	  ((loc lifted-prim) -> (⊥ (lift + (loc seconds) 5) ((loc lifted-prim1))))
	  ((loc seconds) -> (0 input ((loc lifted-prim1) (loc lifted-prim))))
	  ((loc key) -> (⊥ input ())))
	 ((loc lifted-prim1))
	 0)))

(define if-stmt-term-prim
  (term (()
	 (((loc if-dyn) -> (⊥ (dyn (lambda (x) (if x true false)) (loc lifted-prim1) (loc if-fwd)) ()))
	  ((loc if-fwd) -> (⊥ (fwd (loc ⊥)) ()))
	  ((loc lifted-prim1) -> (⊥ (lift < (loc seconds) (loc lifted-prim)) ((loc if-dyn))))
	  ((loc lifted-prim) -> (⊥ (lift + (loc seconds) 5) ((loc lifted-prim1))))
	  ((loc seconds) -> (0 input ((loc lifted-prim1) (loc lifted-prim))))
	  ((loc key) -> (⊥ input ())))
	 ((loc lifted-prim))
	 0)))

(apply-reduction-relation
 ->update
 if-stmt-term-prim)

(module+ test (test-results))
