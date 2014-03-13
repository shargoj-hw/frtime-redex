#lang racket (require redex)

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
     ((σ v n) ...))
  (S ::= 
     ((v -> sis) ...))
  (sis ::=
       (v s (σ ...))))

(define-metafunction FrTime-Semantics
  get-signal-in-store : S v -> sis or #f
  [(get-signal-in-store ((v_1 -> sis_1) ... (v -> sis) (v_2 -> sis_2) ...) v)
   sis
   (side-condition (not (member (term v) (term (v_1 ...)))))]
  [(get-signal-in-store S v) #f])

(define-metafunction FrTime-Semantics
  set-signal-in-store : S v sis -> S
  [(set-signal-in-store ((v_1 -> sis_1) ... (v -> sis_old) (v_2 -> sis_2) ...) v sis)
   ((v_1 -> sis_1) ... (v -> sis) (v_2 -> sis_2) ...)
   (side-condition (not (member (term v) (term (v_1 ...)))))]
  [(set-signal-in-store ((v_1 -> sis_1) ...) v sis)
   ((v -> sis) (v_1 -> sis_1) ...)])

(define-metafunction FrTime-Semantics
  Vs : S v -> v
  [(Vs S v) v_2
   (where (v_2 _ _) (get-signal-in-store S v))])

(define-metafunction FrTime-Semantics
  A : Σ v v -> Σ
  [(A Σ v v) Σ]
  [(A Σ v v_other) ()])

(define-metafunction FrTime-Semantics
  reg : σ Σ S -> S
  [(reg σ () S) S]
  [(reg σ (σ_prime σ_prime2 ...) S) 
   (reg σ (σ_prime2 ...) S_updated)
   (where S_updated (set-signal-in-store S σ_prime (v s (σ σ_prime_set ...))))
   (where (v s (σ_prime_set ...)) (get-signal-in-store S σ_prime))])

(define-metafunction FrTime-Semantics
  Ds : S Σ -> Σ
  [(Ds S Σ) (Ds* S Σ ())])

(define-metafunction FrTime-Semantics
  Ds* : S Σ Σ-> Σ
  [(Ds* S () Σ) ,(remove-duplicates (term Σ))]
  [(Ds* S (σ_first σ_rest ...) (σ_acc ...))
   (Ds* S (σ_rest ...) (σ_first-in-store ... σ_acc ...))
   (where (_ _ (σ_first-in-store ...)) (get-signal-in-store S σ_first))])



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
    (--> (X S (σ_fst ... σ σ_rst ...) t)
         ;; reduces to
         (X S_prime I_prime t)
         (where S_prime (set-signal-in-store S σ (v (fwd σ_prime) Σ)))
	 (where I_prime (σ_a ... σ_fst ... σ_rst ...))
         (where (σ_a ...) (A Σ v_0 v))
         (where (v_0 (fwd σ_prime) Σ) (get-signal-in-store S σ))
         (where (v _ _) (get-signal-in-store S σ_prime))
	 "u-fwd")
    (--> (X S I t)
	 ;; reduces to
	 (X S_1 I_prime-cleaned t)
	 (where (σ_fst ... σ σ_rst ...) I)
	 (where (⊥ (dyn u σ_1 σ_2) Σ) (get-signal-in-store S σ))
	 (where (v (fwd _) Σ_2) (get-signal-in-store S σ_2))
	 (where (S_* ()) (del* S Σ))
	 (where (S_prime I_prime σ_3) 
		(DO-SOME-WEIRD-ARROW-MAGIC S_* I (u (Vs S σ_1))))
	 (where Σ_prime (remove-all (dom S_prime) (dom S)))
	 (where S_updated-fwd (set-signal-in-store S_prime σ_2 (v (fwd σ_3) Σ_2)))
	 (where S_updated-dyn (set-signal-in-store S_updated-fwd σ (⊥ (dyn u σ_1 σ_2) Σ_prime)))
	 (where S_1 (reg σ_2 (σ_3) S_updated-dyn))
	 (where I_prime-cleaned (remove-all (remove-all I Σ) (σ)))
	 "u-dyn")))
    
