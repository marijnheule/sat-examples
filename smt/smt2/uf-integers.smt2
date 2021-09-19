(declare-fun out0_a () (_ BitVec 128))
(declare-fun out1_a () (_ BitVec 128))
(declare-fun in0_a () (_ BitVec 128))
(declare-fun out2_a () (_ BitVec 128))
(declare-fun out0_b () (_ BitVec 128))
(declare-fun in0_b () (_ BitVec 128))
(declare-fun f ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))
(define-fun phi_a () Bool
	(and (= out0_a in0_a) ; out0_a = in0_a
		(and (= out1_a (f out0_a in0_a)) ; out1_a = out0_a * in0_a
			(= out2_a (f out1_a in0_a))))) ; out2_a = out1_a * in0_a
(define-fun phi_b () Bool
	(= out0_b (f (f in0_b in0_b) in0_b))) ; out0_b = in0_b * in0_b * in0_b
(define-fun phi_input () Bool 
	(= in0_a in0_b))
(define-fun phi_output () Bool
	(= out2_a out0_b ))
(assert (not (=> (and phi_input phi_a phi_b) phi_output )))
(check-sat)
