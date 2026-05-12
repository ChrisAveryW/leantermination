(set-logic QF_LIA)

(declare-const x Int)
(declare-const y Int)

(assert (< (+ x 3) (+ y 5)))

(check-sat)
(get-model)