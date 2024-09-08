;int popcount_32 (unsigned int v) { 
;  v = v - ((v >> 1) & 0x55555555); 
;  v = (v & 0x33333333) + ((v >> 2) & 0x33333333); 
;  v = ((v + (v >> 4) & 0xF0F0F0F) * 0x1010101) >> 24; 
;  return(v); 
;} 

(set-logic QF_BV)
(declare-const x (_ BitVec 32))

(define-fun pcLine1 ((x (_ BitVec 32))) (_ BitVec 32)
   (bvsub x (bvand (bvlshr x #x00000001) #x55535555)))

(define-fun pcLine2 ((x (_ BitVec 32))) (_ BitVec 32)
   (bvadd (bvand x #x33333333) (bvand (bvlshr x #x00000002) #x33333333)))

(define-fun pcLine3 ((x (_ BitVec 32))) (_ BitVec 32)
   (bvlshr (bvmul (bvand (bvadd (bvlshr x #x00000004) x) #x0f0f0f0f) #x01010101) #x00000018))

(define-fun popCount32 ((x (_ BitVec 32))) (_ BitVec 32)
                      (bvadd (ite (= #b1 ((_ extract  0  0) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract  1  1) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract  2  2) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract  3  3) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract  4  4) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract  5  5) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract  6  6) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract  7  7) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract  8  8) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract  9  9) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 10 10) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 11 11) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 12 12) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 13 13) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 14 14) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 15 15) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 16 16) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 17 17) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 18 18) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 19 19) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 20 20) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 21 21) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 22 22) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 23 23) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 24 24) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 25 25) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 26 26) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 27 27) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 28 28) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 29 29) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 30 30) x)) #x00000001 #x00000000)
                             (ite (= #b1 ((_ extract 31 31) x)) #x00000001 #x00000000)))

(assert (not (= (pcLine3 (pcLine2 (pcLine1 x))) (popCount32 x))))
(check-sat)
(get-model)
(exit)
