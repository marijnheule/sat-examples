(set-logic QF_LIA)
   (declare-const x Int)
   (declare-const y Int)
   (assert (> x y))
   (check-sat) ; should be SAT
   (get-model)
(exit)
