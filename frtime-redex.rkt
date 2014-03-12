#lang racket (require redex)

(define-language FrTime
  ;; Store locations
  ;; TODO: is this right?
  (SIGMA (loc n))

  ;; Variables
  (x variable-not-otherwise-mentioned)
  ;; Primatives
  (p + - * / < >)
  ;; Values
  ((u v)
   UNDEFINED true false n p (lambda (x ...) e) SIGMA)
  ;; Numbers
  (n number)
  ;; Expressions
  (e v x (e e ...) (delay e n) (if e e e))

  ;; Contexts
  (E hole (v ... E e ...) (delay E n) (if E e e))

  ;; Signal Types
  (s (lift p v ...)
     (delay SIMGA n SIGMA)
     (dyn (lambda (v) e) SIGMA SIGMA)
     (fwd SIGMA)
     input
     const))

(define ->construction
  (reduction-relation 
    FrTime
    #:domain (S I e)
    (--> (S I (in-hole e (p v ...)))
         ;; reduces to
         (S I (in-hole v_applied)) 
         (side-condition (andmap (lambda (x) (not (redex-match? FrTime SIGMA x)))
                                 (term (v ...))))
         (where v_applied (DELTA p v ...))
         "primitive-application")
    (--> (S (i ...) (in-hole E (p v ...))) 
         ;; reduces to
         (S_prime (SIGMA i ...) (in-hole E SIGMA))
         (where (SIGMA_arg ...) 
                ,(filter (lambda (x) (redex-match? FrTime SIGMA x))
                         (term (v ...))))
         (side-condition (not (empty? (term SIGMA_args))))
         (where S_prime 
                (reg SIGMA 
                     (SIGMA_arg ...)
                     (set-signal-in-store S SIGMA (undefined (lift p v ...) ()))))
         "primitive-lift")
    (--> (S I (in-hole E ((lambda (x ..._n) e) v ..._n)))
            ;; reduces to
         (S I (in-hole E (subst-n (x v) ... e)))
         "beta-v")
    (--> (S (i ...) (in-hole E (SIGMA v ...)))
         ;; reduces to
         ((reg SIGMA_1 (SIGMA) S_prime)
          (SIGMA_1 i ...)
          (in-hole E SIGMA_2))
         (where S_prime 
                (set-signal-in-store S_half_prime 
                                     SIGMA_1 
                                     (undefined 
                                      (dyn (lambda (x) (x v ...))
                                           SIGMA 
                                           SIGMA_2)
                                      ())))
         (where S_half_prime 
                (set-signal-in-store S 
                                     SIGMA_2 
                                     (undefined (fwd undefined) ())))
         "beta-v-lift")
    (--> (S I (in-hole E (if true e_1 e_2)))
         ;; reduces to
         (S I (in-hole E e_1))
         "if-true")
    (--> (S I (in-hole E (if false e_1 e_2)))
         ;; reduces to
         (S I (in-hole E e_2))
         "if-false")
    (--> (S I (in-hole E (if SIGMA e_1 e_2)))
         ((reg SIGMA_1 (SIGMA) S_prime)
          (SIGMA_1 i ...)
          (in-hole E SIGMA_2))
         (where S_prime 
                (set-signal-in-store S_half_prime 
                                     SIGMA_1 
                                     (undefined 
                                       (dyn (lambda (x) (if x e_1 e_2))
                                            SIGMA 
                                            SIGMA_2)
                                       ())))
         (where S_half_prime 
                (set-signal-in-store S 
                                     SIGMA_2 
                                     (undefined (fwd undefined) ())))
         "if-lift") 
    (--> (S (i ...) (in-hole E (delay SIGMA n)))
         ;; reduces to 
         (S_prime (SIGMA_2 i ...) (in-hole E SIGMA_1))
         (where S_half_prime
                (set-signal-in-store S
                                     SIGMA_2
                                     (undefined
                                      (delay SIGMA n SIGMA_1)
                                      ())))
         (where S_almost_prime
                (set-signal-in-store S_half_prime
                                     SIGMA_1
                                     (undefined input ())))
         (where S_prime (reg SIGMA_2 (SIGMA) S_almost_prime))
         "delay")))
;; to-write - reg, DELTA, lift, signal-in-store
