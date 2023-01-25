(declare-fun x1_{id} () (_ BitVec 8))
(assert (= x1_{id} (bvor (bvlshr {x} #x04) (bvshl {x} #x04))))

(declare-fun x2_{id} () (_ BitVec 8))
(assert (= x2_{id} (bvor (bvlshr (bvand x1_{id} #xcc) #x02) (bvshl (bvand x1_{id} #x33) #x02))))

(declare-fun rev8ret_{id} () (_ BitVec 8))
(assert (= rev8ret_{id} (bvor (bvlshr (bvand x2_{id} #xaa) #x01) (bvshl (bvand x2_{id} #x55) #x01))))
