(declare-fun x1_{id} () (_ BitVec 32))
(assert (= x1_{id} (bvor (bvlshr {x} #x00000010) (bvshl {x} #x00000010))))

(declare-fun x2_{id} () (_ BitVec 32))
(assert (= x2_{id} (bvor (bvlshr (bvand x1_{id} #xff00ff00) #x00000008) (bvshl (bvand x1_{id} #x00ff00ff) #x00000008))))

(declare-fun x3_{id} () (_ BitVec 32))
(assert (= x3_{id} (bvor (bvlshr (bvand x2_{id} #xf0f0f0f0) #x00000004) (bvshl (bvand x2_{id} #x0f0f0f0f) #x00000004))))

(declare-fun x4_{id} () (_ BitVec 32))
(assert (= x4_{id} (bvor (bvlshr (bvand x3_{id} #xcccccccc) #x00000002) (bvshl (bvand x3_{id} #x33333333) #x00000002))))

(declare-fun rev32ret_{id} () (_ BitVec 32))
(assert (= rev32ret_{id} (bvor (bvlshr (bvand x4_{id} #xaaaaaaaa) #x00000001) (bvshl (bvand x4_{id} #x55555555) #x00000001))))
