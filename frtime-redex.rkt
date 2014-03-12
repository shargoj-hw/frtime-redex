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
   UNDEFINED true false n p (λ (x ...) e) SIGMA)
  ;; Numbers
  (n number)
  ;; Expressions
  (e v x (e e ...) (delay e n) (if e e e))

  ;; Contexts
  (E hole (v ... E e ...) (delay E n) (if E e e))

  ;; Signal Types
  (s (lift p v ...)
     (delay SIMGA n SIGMA)
     (dyn (λ (v) e) SGIMA SIGMA)
     (fwd SIGMA)
     input
     const))

