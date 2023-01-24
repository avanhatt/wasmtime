(declare-fun x1_{id} () (_ BitVec 16))
(assert (= x1_{id} (bvor (bvlshr {x} #x0008) (bvshl {x} #x0008))))

(declare-fun x2_{id} () (_ BitVec 16))
(assert (= x2_{id} (bvor (bvlshr (bvand x1_{id} #xf0f0) #x0004) (bvshl (bvand x1_{id} #x0f0f) #x0004))))

(declare-fun x3_{id} () (_ BitVec 16))
(assert (= x3_{id} (bvor (bvlshr (bvand x2_{id} #xcccc) #x0002) (bvshl (bvand x2_{id} #x3333) #x0002))))

(declare-fun rev16ret_{id} () (_ BitVec 16))
(assert (= rev16ret_{id} (bvor (bvlshr (bvand x3_{id} #xaaaa) #x0001) (bvshl (bvand x3_{id} #x5555) #x0001))))
