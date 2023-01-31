(declare-fun x1_{id} () (_ BitVec 64))
(assert (= x1_{id} (bvor (bvlshr {x} #x0000000000000020) (bvshl {x} #x0000000000000020))))

(declare-fun x2_{id} () (_ BitVec 64))
(assert (= x2_{id} (bvor (bvlshr (bvand x1_{id} #xffff0000ffff0000) #x0000000000000010) (bvshl (bvand x1_{id} #x0000ffff0000ffff) #x0000000000000010))))

(declare-fun x3_{id} () (_ BitVec 64))
(assert (= x3_{id} (bvor (bvlshr (bvand x2_{id} #xff00ff00ff00ff00) #x0000000000000008) (bvshl (bvand x2_{id} #x00ff00ff00ff00ff) #x0000000000000008))))

(declare-fun x4_{id} () (_ BitVec 64))
(assert (= x4_{id} (bvor (bvlshr (bvand x3_{id} #xf0f0f0f0f0f0f0f0) #x0000000000000004) (bvshl (bvand x3_{id} #x0f0f0f0f0f0f0f0f) #x0000000000000004))))

(declare-fun x5_{id} () (_ BitVec 64))
(assert (= x5_{id} (bvor (bvlshr (bvand x4_{id} #xcccccccccccccccc) #x0000000000000002) (bvshl (bvand x4_{id} #x3333333333333333) #x0000000000000002))))

(declare-fun rev64ret_{id} () (_ BitVec 64))
(assert (= rev64ret_{id} (bvor (bvlshr (bvand x5_{id} #xaaaaaaaaaaaaaaaa) #x0000000000000001) (bvshl (bvand x5_{id} #x5555555555555555) #x0000000000000001))))
