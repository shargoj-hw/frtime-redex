#lang racket (require redex rackunit)

(define-language FrTime
  ;; Store locations
  ;; TODO: is this right?
  (σ (loc n))

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
     (dyn (lambda (v) e) σ σ)
     (fwd σ)
     input
     const))

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
       (v s (σ ...))))

(module+ test
  (define S1
    (term (((loc 0) -> (4 (lift + 3 (loc 4)) ()))
	   ((loc 4) -> (2 const ((loc 0)))))))
  (define S2 
    (term (((loc 4) -> (⊥ const ()))
	   ((loc 2) -> (94 const ((loc 80))))
	   ((loc 3) -> (20 input ((loc 20)))))))
  (define S3
    (term (((loc 4) -> (⊥ const ((loc 9))))
	   ((loc 2) -> (94 const ((loc 9) (loc 80))))
	   ((loc 3) -> (20 input ((loc 20)))))))
  (define Σ1 (term ((loc 0) (loc 3) (loc 9))))

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
  [(δ < n ...) ,(apply < (term (n ...)))]
  [(δ > n ...) ,(apply > (term (n ...)))]
  [(δ p v ...) ,(error 'δ "primitive application not supported!")])

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
  (test-equal (term (get-signal-in-store ,S1 (loc 4)))
	      (term (2 const ((loc 0)))))
  (test-equal (term (get-signal-in-store ,S1 (loc 99)))
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
  (test-equal (term (set-signal-in-store ,S1 (loc 0) (309 const ())))
	      (term (((loc 0) -> (309 const ()))
		     ((loc 4) -> (2 const ((loc 0)))))))
  (test-equal (term (set-signal-in-store ,S1 (loc 9) (309 const ())))
	      (term (((loc 9) -> (309 const ()))
		     ((loc 0) -> (4 (lift + 3 (loc 4)) ()))
		     ((loc 4) -> (2 const ((loc 0))))))))

;; Vs : S v -> v
;; Get the current value of the given sigma
(define-metafunction FrTime-Semantics
  Vs : S v -> v
  [(Vs S v) v_2
   (where (v_2 s_any Σ_any) (get-signal-in-store S v))])

(module+ test
  (test-equal (term (Vs ,S1 (loc 0))) 4)
  (test-equal (term (Vs ,S1 (loc 4))) 2))

;; A : Σ v v -> Σ
;; Returns Sigma if the values are equal, or the empty list 
;; otherwise
(define-metafunction FrTime-Semantics
  A : Σ v v -> Σ
  [(A Σ v v) Σ]
  [(A Σ v v_other) ()])

(module+ test
  (test-equal (term (A ,Σ1 (lambda (x) x) (lambda (x) x))) Σ1)
  (test-equal (term (A ,Σ1 (lambda (x) x) (loc 5))) (term ())))

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
  (test-equal (term (reg (loc 9) ((loc 4) (loc 2)) ,S2)) S3))

;; Ds : S Σ -> Σ
;; Returns the set of the union of all dependencies for each σ ∈ Σ
(define-metafunction FrTime-Semantics
  Ds : S Σ -> Σ
  [(Ds S Σ) (Ds* S Σ ())])

(module+ test
  (test-equal (term (Ds ,S2 ((loc 9)))) (term ()))
  (test-equal (term (Ds ,S2 ((loc 2) (loc 3)))) (term ((loc 20) (loc 80)))))

;; Helper function for Ds. Accummulates values in the second sigma and
;; setifies them once they're all collected.
(define-metafunction FrTime-Semantics
  Ds* : S Σ Σ -> Σ
  [(Ds* S () Σ) ,(remove-duplicates (term Σ))]
  [(Ds* S (σ_first σ_rest ...) (σ_acc ...))
   (Ds* S (σ_rest ...) (σ_first-in-store ... σ_acc ...))
   (where (v_any s_any (σ_first-in-store ...)) (get-signal-in-store S σ_first))]
  [(Ds* S (σ_first σ_rest ...) Σ) (Ds* S (σ_rest ...) Σ)])

(define ->construction
  (reduction-relation 
   FrTime-Semantics
   #:domain (S I e)
   (--> (S I (in-hole E (p v ...)))
        ;; reduces to
        (S I (in-hole E v_applied)) 
        (side-condition (andmap (lambda (x) (not (redex-match? FrTime σ x)))
                                (term (v ...))))
        (where v_applied (DELTA p v ...))
        "primitive-application")
   (--> (S (i ...) (in-hole E (p v ...))) 
        ;; reduces to
        (S_prime (σ i ...) (in-hole E σ))
        (where (σ_arg ...) 
               ,(filter (lambda (x) (redex-match? FrTime σ x))
                        (term (v ...))))
        (side-condition (not (empty? (term σ_args))))
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
        (where S_prime 
               (set-signal-in-store S_halfprime 
                                    σ_1 
                                    (⊥ 
                                     (dyn (lambda (x) (x v ...))
                                          σ 
                                          σ_2)
                                     ())))
        (where S_halfprime 
               (set-signal-in-store S 
                                    σ_2 
                                    (⊥ (fwd ⊥) ())))
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
        (where S_prime 
               (set-signal-in-store S_halfprime σ_1 (⊥ dyn-term ())))
        (where dyn-term
               (dyn (lambda (x) (if x e_1 e_2)) σ  σ_2))
        (where S_halfprime 
               (set-signal-in-store S σ_2 (⊥ (fwd ⊥) ())))
        "if-lift") 
   (--> (S (i ...) (in-hole E (delay σ n)))
        ;; reduces to 
        (S_prime (σ_2 i ...) (in-hole E σ_1))
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
         (where S_prime (set-signal-in-store S σ (v (fwd σ_prime) Σ)))
         (where (σ_a ...) (A Σ v_0 v))
         (where I_prime (σ_a ... i_fst ... i_rst ...))
         (where (v_0 (fwd σ_prime) Σ) (get-signal-in-store S σ))
         (where (v s_any Σ_any) (get-signal-in-store S σ_prime))
         "u-fwd")
    (--> (X S I t)
         ;; reduces to
         (X S_1 I_prime-cleaned t)
         (where (i_fst ... σ i_rst ...) I)
         (where (⊥ (dyn u σ_1 σ_2) Σ) (get-signal-in-store S σ))
         (where (v (fwd σ_any) Σ_2) (get-signal-in-store S σ_2))
         (where (S_* ()) (del* S Σ))
         (where (S_prime I_prime σ_3) 
                (DO-SOME-WEIRD-ARROW-MAGIC S_* I (u (Vs S σ_1))))
         (where Σ_prime (remove-all (dom S_prime) (dom S)))
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
         (where X_prime ((σ_1 (Vs S σ) ,(+ (term t) (term n))) xs ...))
         (where I_prime (i_fst ... i_rst ...))
         (where (⊥ (delay σ n σ_1) Σ) (get-signal-in-store S σ))
         "u-delay")
    (--> (X S I t)
         ;; reduces to
         (X S_prime I_prime t)
         (where (i_fst ... σ i_rst ...) I)
         (side-condition (not (member (term σ) (term (dfrd S I)))))
         (where (v_0 (lift p v_1 ...) Σ) (get-signal-in-store S σ))
         (where v (δ p (Vs v_1) ...))
         (where S_prime (set-signal-in-store S σ (v (lift p v_1 ...) Σ)))
         (where (σ_a ...) (A Σ v_0 v))
         (where I_prime (σ_a ... i_fst ... i_rst ...))
         "u-lift")))
    
(module+ test (test-results))
