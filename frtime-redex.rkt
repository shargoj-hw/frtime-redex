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
     (delay SIMGA n σ)
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
  reg : σ Σ S -> S
  [(reg σ () S) S]
  [(reg σ (σ_prime σ_prime2 ...) S) 
   (reg σ (σ_prime2 ...) S_updated)
   (where S_updated (set-signal-in-store S σ_prime (v s (σ σ_prime_set ...))))
   (where (v s (σ_prime_set ...)) (get-signal-in-store S σ_prime))])

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
;; to-write - reg, DELTA, lift, signal-in-store
