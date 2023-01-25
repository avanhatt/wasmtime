; total zeros counter
(declare-fun zret0_{id} () (_ BitVec 8))
(assert (= zret0_{id} (_ bv0 8)))

; round 1
(declare-fun zret4_{id} () (_ BitVec 8))
(declare-fun zy4_{id} () (_ BitVec 8))
(declare-fun zx4_{id} () (_ BitVec 8))

(assert (= zy4_{id} (bvlshr {x} #x04)))
(assert (ite (not (= zy4_{id} (_ bv0 8))) (= zret4_{id} zret0_{id}) (= zret4_{id} (bvadd zret0_{id} (_ bv4 8)))))
(assert (ite (not (= zy4_{id} (_ bv0 8))) (= zx4_{id} zy4_{id}) (= zx4_{id} {x})))

; round 2
(declare-fun zret5_{id} () (_ BitVec 8))
(declare-fun zy2_{id} () (_ BitVec 8))
(declare-fun zx2_{id} () (_ BitVec 8))

(assert (= zy2_{id} (bvlshr zx4_{id} #x02)))
(assert (ite (not (= zy2_{id} (_ bv0 8))) (= zret5_{id} zret4_{id}) (= zret5_{id} (bvadd zret4_{id} (_ bv2 8)))))
(assert (ite (not (= zy2_{id} (_ bv0 8))) (= zx2_{id} zy2_{id}) (= zx2_{id} zx4_{id})))

; round 3
(declare-fun zret6_{id} () (_ BitVec 8))
(declare-fun zy1_{id} () (_ BitVec 8))
(declare-fun zx1_{id} () (_ BitVec 8))

(assert (= zy1_{id} (bvlshr zx2_{id} #x01)))
(assert (ite (not (= zy1_{id} (_ bv0 8))) (= zret6_{id} zret5_{id}) (= zret6_{id} (bvadd zret5_{id} (_ bv1 8)))))
(assert (ite (not (= zy1_{id} (_ bv0 8))) (= zx1_{id} zy1_{id}) (= zx1_{id} zx2_{id})))

; last round
(declare-fun zret7_{id} () (_ BitVec 8))
(assert (ite (not (= zx1_{id} (_ bv0 8))) (= zret7_{id} zret6_{id}) (= zret7_{id} (bvadd zret6_{id} (_ bv1 8)))))

(declare-fun clzret_{id} () (_ BitVec 8))
(assert (ite (= zret7_{id} (_ bv0 8)) (= clzret_{id} zret7_{id}) (= clzret_{id} (bvsub zret7_{id} (_ bv1 8)))))






; total zeros counter
(declare-fun sret0_{id} () (_ BitVec 8))
(assert (= sret0_{id} (_ bv0 8)))

; round 1
(declare-fun sret4_{id} () (_ BitVec 8))
(declare-fun sy4_{id} () (_ BitVec 8))
(declare-fun sx4_{id} () (_ BitVec 8))

(assert (= sy4_{id} (bvashr {x} #x04)))
(assert (ite (not (= sy4_{id} (_ bv255 8))) (= sret4_{id} sret0_{id}) (= sret4_{id} (bvadd sret0_{id} (_ bv4 8)))))
(assert (ite (not (= sy4_{id} (_ bv255 8))) (= sx4_{id} sy4_{id}) (= sx4_{id} {x})))

; round 2
(declare-fun sret5_{id} () (_ BitVec 8))
(declare-fun sy2_{id} () (_ BitVec 8))
(declare-fun sx2_{id} () (_ BitVec 8))

(assert (= sy2_{id} (bvashr sx4_{id} #x02)))
(assert (ite (not (= sy2_{id} (_ bv255 8))) (= sret5_{id} sret4_{id}) (= sret5_{id} (bvadd sret4_{id} (_ bv2 8)))))
(assert (ite (not (= sy2_{id} (_ bv255 8))) (= sx2_{id} sy2_{id}) (= sx2_{id} sx4_{id})))

; round 3
(declare-fun sret6_{id} () (_ BitVec 8))
(declare-fun sy1_{id} () (_ BitVec 8))
(declare-fun sx1_{id} () (_ BitVec 8))

(assert (= sy1_{id} (bvashr sx2_{id} #x01)))
(assert (ite (not (= sy1_{id} (_ bv255 8))) (= sret6_{id} sret5_{id}) (= sret6_{id} (bvadd sret5_{id} (_ bv1 8)))))
(assert (ite (not (= sy1_{id} (_ bv255 8))) (= sx1_{id} sy1_{id}) (= sx1_{id} sx2_{id})))

; last round
(declare-fun sret7_{id} () (_ BitVec 8))
(assert (ite (not (= sx1_{id} (_ bv255 8))) (= sret7_{id} sret6_{id}) (= sret7_{id} (bvadd sret6_{id} (_ bv1 8)))))

(declare-fun clsret_{id} () (_ BitVec 8))
(assert (ite (= sret7_{id} (_ bv0 8)) (= clsret_{id} sret7_{id}) (= clsret_{id} (bvsub sret7_{id} (_ bv1 8)))))





(declare-fun cls8ret_{id} () (_ BitVec 8))
(assert (ite (bvsle (_ bv0 8) {x}) (= cls8ret_{id} clzret_{id}) (= cls8ret_{id} clsret_{id})))
