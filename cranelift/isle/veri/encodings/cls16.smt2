; total zeros counter
(declare-fun zret0_{id} () (_ BitVec 16))
(assert (= zret0_{id} (_ bv0 16)))

; round 1
(declare-fun zret3_{id} () (_ BitVec 16))
(declare-fun zy8_{id} () (_ BitVec 16))
(declare-fun zx8_{id} () (_ BitVec 16))

(assert (= zy8_{id} (bvlshr {x} #x0008)))
(assert (ite (not (= zy8_{id} (_ bv0 16))) (= zret3_{id} zret0_{id}) (= zret3_{id} (bvadd zret0_{id} (_ bv8 16)))))
(assert (ite (not (= zy8_{id} (_ bv0 16))) (= zx8_{id} zy8_{id}) (= zx8_{id} {x})))

; round 2
(declare-fun zret4_{id} () (_ BitVec 16))
(declare-fun zy4_{id} () (_ BitVec 16))
(declare-fun zx4_{id} () (_ BitVec 16))

(assert (= zy4_{id} (bvlshr zx8_{id} #x0004)))
(assert (ite (not (= zy4_{id} (_ bv0 16))) (= zret4_{id} zret3_{id}) (= zret4_{id} (bvadd zret3_{id} (_ bv4 16)))))
(assert (ite (not (= zy4_{id} (_ bv0 16))) (= zx4_{id} zy4_{id}) (= zx4_{id} zx8_{id})))

; round 3
(declare-fun zret5_{id} () (_ BitVec 16))
(declare-fun zy2_{id} () (_ BitVec 16))
(declare-fun zx2_{id} () (_ BitVec 16))

(assert (= zy2_{id} (bvlshr zx4_{id} #x0002)))
(assert (ite (not (= zy2_{id} (_ bv0 16))) (= zret5_{id} zret4_{id}) (= zret5_{id} (bvadd zret4_{id} (_ bv2 16)))))
(assert (ite (not (= zy2_{id} (_ bv0 16))) (= zx2_{id} zy2_{id}) (= zx2_{id} zx4_{id})))

; round 4
(declare-fun zret6_{id} () (_ BitVec 16))
(declare-fun zy1_{id} () (_ BitVec 16))
(declare-fun zx1_{id} () (_ BitVec 16))

(assert (= zy1_{id} (bvlshr zx2_{id} #x0001)))
(assert (ite (not (= zy1_{id} (_ bv0 16))) (= zret6_{id} zret5_{id}) (= zret6_{id} (bvadd zret5_{id} (_ bv1 16)))))
(assert (ite (not (= zy1_{id} (_ bv0 16))) (= zx1_{id} zy1_{id}) (= zx1_{id} zx2_{id})))

; last round
(declare-fun zret7_{id} () (_ BitVec 16))
(assert (ite (not (= zx1_{id} (_ bv0 16))) (= zret7_{id} zret6_{id}) (= zret7_{id} (bvadd zret6_{id} (_ bv1 16)))))

(declare-fun clzret_{id} () (_ BitVec 16))
(assert (ite (= zret7_{id} (_ bv0 16)) (= clzret_{id} zret7_{id}) (= clzret_{id} (bvsub zret7_{id} (_ bv1 16)))))






; total zeros counter
(declare-fun sret0_{id} () (_ BitVec 16))
(assert (= sret0_{id} (_ bv0 16)))

; round 1
(declare-fun sret3_{id} () (_ BitVec 16))
(declare-fun sy8_{id} () (_ BitVec 16))
(declare-fun sx8_{id} () (_ BitVec 16))

(assert (= sy8_{id} (bvashr {x} #x0008)))
(assert (ite (not (= sy8_{id} (_ bv65535 16))) (= sret3_{id} sret0_{id}) (= sret3_{id} (bvadd sret0_{id} (_ bv8 16)))))
(assert (ite (not (= sy8_{id} (_ bv65535 16))) (= sx8_{id} sy8_{id}) (= sx8_{id} {x})))

; round 2
(declare-fun sret4_{id} () (_ BitVec 16))
(declare-fun sy4_{id} () (_ BitVec 16))
(declare-fun sx4_{id} () (_ BitVec 16))

(assert (= sy4_{id} (bvashr sx8_{id} #x0004)))
(assert (ite (not (= sy4_{id} (_ bv65535 16))) (= sret4_{id} sret3_{id}) (= sret4_{id} (bvadd sret3_{id} (_ bv4 16)))))
(assert (ite (not (= sy4_{id} (_ bv65535 16))) (= sx4_{id} sy4_{id}) (= sx4_{id} sx8_{id})))

; round 3
(declare-fun sret5_{id} () (_ BitVec 16))
(declare-fun sy2_{id} () (_ BitVec 16))
(declare-fun sx2_{id} () (_ BitVec 16))

(assert (= sy2_{id} (bvashr sx4_{id} #x0002)))
(assert (ite (not (= sy2_{id} (_ bv65535 16))) (= sret5_{id} sret4_{id}) (= sret5_{id} (bvadd sret4_{id} (_ bv2 16)))))
(assert (ite (not (= sy2_{id} (_ bv65535 16))) (= sx2_{id} sy2_{id}) (= sx2_{id} sx4_{id})))

; round 4
(declare-fun sret6_{id} () (_ BitVec 16))
(declare-fun sy1_{id} () (_ BitVec 16))
(declare-fun sx1_{id} () (_ BitVec 16))

(assert (= sy1_{id} (bvashr sx2_{id} #x0001)))
(assert (ite (not (= sy1_{id} (_ bv65535 16))) (= sret6_{id} sret5_{id}) (= sret6_{id} (bvadd sret5_{id} (_ bv1 16)))))
(assert (ite (not (= sy1_{id} (_ bv65535 16))) (= sx1_{id} sy1_{id}) (= sx1_{id} sx2_{id})))

; last round
(declare-fun sret7_{id} () (_ BitVec 16))
(assert (ite (not (= sx1_{id} (_ bv65535 16))) (= sret7_{id} sret6_{id}) (= sret7_{id} (bvadd sret6_{id} (_ bv1 16)))))

(declare-fun clsret_{id} () (_ BitVec 16))
(assert (ite (= sret7_{id} (_ bv0 16)) (= clsret_{id} sret7_{id}) (= clsret_{id} (bvsub sret7_{id} (_ bv1 16)))))





(declare-fun cls16ret_{id} () (_ BitVec 16))
(assert (ite (bvsle (_ bv0 16) {x}) (= cls16ret_{id} clzret_{id}) (= cls16ret_{id} clsret_{id})))
