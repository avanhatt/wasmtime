; total zeros counter
(declare-fun zret0_{id} () (_ BitVec 64))
(assert (= zret0_{id} (_ bv0 64)))

; round 1
(declare-fun zret1_{id} () (_ BitVec 64))
(declare-fun zy32_{id} () (_ BitVec 64))
(declare-fun zx32_{id} () (_ BitVec 64))

(assert (= zy32_{id} (bvlshr {x} #x0000000000000020)))
(assert (ite (not (= zy32_{id} (_ bv0 64))) (= zret1_{id} zret0_{id}) (= zret1_{id} (bvadd zret0_{id} (_ bv32 64)))))
(assert (ite (not (= zy32_{id} (_ bv0 64))) (= zx32_{id} zy32_{id}) (= zx32_{id} {x})))

; round 2
(declare-fun zret2_{id} () (_ BitVec 64))
(declare-fun zy16_{id} () (_ BitVec 64))
(declare-fun zx16_{id} () (_ BitVec 64))

(assert (= zy16_{id} (bvlshr zx32_{id} #x0000000000000010)))
(assert (ite (not (= zy16_{id} (_ bv0 64))) (= zret2_{id} zret1_{id}) (= zret2_{id} (bvadd zret1_{id} (_ bv16 64)))))
(assert (ite (not (= zy16_{id} (_ bv0 64))) (= zx16_{id} zy16_{id}) (= zx16_{id} zx32_{id})))

; round 3
(declare-fun zret3_{id} () (_ BitVec 64))
(declare-fun zy8_{id} () (_ BitVec 64))
(declare-fun zx8_{id} () (_ BitVec 64))

(assert (= zy8_{id} (bvlshr zx16_{id} #x0000000000000008)))
(assert (ite (not (= zy8_{id} (_ bv0 64))) (= zret3_{id} zret2_{id}) (= zret3_{id} (bvadd zret2_{id} (_ bv8 64)))))
(assert (ite (not (= zy8_{id} (_ bv0 64))) (= zx8_{id} zy8_{id}) (= zx8_{id} zx16_{id})))

; round 4
(declare-fun zret4_{id} () (_ BitVec 64))
(declare-fun zy4_{id} () (_ BitVec 64))
(declare-fun zx4_{id} () (_ BitVec 64))

(assert (= zy4_{id} (bvlshr zx8_{id} #x0000000000000004)))
(assert (ite (not (= zy4_{id} (_ bv0 64))) (= zret4_{id} zret3_{id}) (= zret4_{id} (bvadd zret3_{id} (_ bv4 64)))))
(assert (ite (not (= zy4_{id} (_ bv0 64))) (= zx4_{id} zy4_{id}) (= zx4_{id} zx8_{id})))

; round 5
(declare-fun zret5_{id} () (_ BitVec 64))
(declare-fun zy2_{id} () (_ BitVec 64))
(declare-fun zx2_{id} () (_ BitVec 64))

(assert (= zy2_{id} (bvlshr zx4_{id} #x0000000000000002)))
(assert (ite (not (= zy2_{id} (_ bv0 64))) (= zret5_{id} zret4_{id}) (= zret5_{id} (bvadd zret4_{id} (_ bv2 64)))))
(assert (ite (not (= zy2_{id} (_ bv0 64))) (= zx2_{id} zy2_{id}) (= zx2_{id} zx4_{id})))

; round 6
(declare-fun zret6_{id} () (_ BitVec 64))
(declare-fun zy1_{id} () (_ BitVec 64))
(declare-fun zx1_{id} () (_ BitVec 64))

(assert (= zy1_{id} (bvlshr zx2_{id} #x0000000000000001)))
(assert (ite (not (= zy1_{id} (_ bv0 64))) (= zret6_{id} zret5_{id}) (= zret6_{id} (bvadd zret5_{id} (_ bv1 64)))))
(assert (ite (not (= zy1_{id} (_ bv0 64))) (= zx1_{id} zy1_{id}) (= zx1_{id} zx2_{id})))

; last round
(declare-fun zret7_{id} () (_ BitVec 64))
(assert (ite (not (= zx1_{id} (_ bv0 64))) (= zret7_{id} zret6_{id}) (= zret7_{id} (bvadd zret6_{id} (_ bv1 64)))))

(declare-fun clzret_{id} () (_ BitVec 64))
(assert (ite (= zret7_{id} (_ bv0 64)) (= clzret_{id} zret7_{id}) (= clzret_{id} (bvsub zret7_{id} (_ bv1 64)))))






; total zeros counter
(declare-fun sret0_{id} () (_ BitVec 64))
(assert (= sret0_{id} (_ bv0 64)))

; round 1
(declare-fun sret1_{id} () (_ BitVec 64))
(declare-fun sy32_{id} () (_ BitVec 64))
(declare-fun sx32_{id} () (_ BitVec 64))

(assert (= sy32_{id} (bvashr {x} #x0000000000000020)))
(assert (ite (not (= sy32_{id} (_ bv18446744073709551615 64))) (= sret1_{id} sret0_{id}) (= sret1_{id} (bvadd sret0_{id} (_ bv32 64)))))
(assert (ite (not (= sy32_{id} (_ bv18446744073709551615 64))) (= sx32_{id} sy32_{id}) (= sx32_{id} {x})))

; round 2
(declare-fun sret2_{id} () (_ BitVec 64))
(declare-fun sy16_{id} () (_ BitVec 64))
(declare-fun sx16_{id} () (_ BitVec 64))

(assert (= sy16_{id} (bvashr sx32_{id} #x0000000000000010)))
(assert (ite (not (= sy16_{id} (_ bv18446744073709551615 64))) (= sret2_{id} sret1_{id}) (= sret2_{id} (bvadd sret1_{id} (_ bv16 64)))))
(assert (ite (not (= sy16_{id} (_ bv18446744073709551615 64))) (= sx16_{id} sy16_{id}) (= sx16_{id} sx32_{id})))

; round 3
(declare-fun sret3_{id} () (_ BitVec 64))
(declare-fun sy8_{id} () (_ BitVec 64))
(declare-fun sx8_{id} () (_ BitVec 64))

(assert (= sy8_{id} (bvashr sx16_{id} #x0000000000000008)))
(assert (ite (not (= sy8_{id} (_ bv18446744073709551615 64))) (= sret3_{id} sret2_{id}) (= sret3_{id} (bvadd sret2_{id} (_ bv8 64)))))
(assert (ite (not (= sy8_{id} (_ bv18446744073709551615 64))) (= sx8_{id} sy8_{id}) (= sx8_{id} sx16_{id})))

; round 4
(declare-fun sret4_{id} () (_ BitVec 64))
(declare-fun sy4_{id} () (_ BitVec 64))
(declare-fun sx4_{id} () (_ BitVec 64))

(assert (= sy4_{id} (bvashr sx8_{id} #x0000000000000004)))
(assert (ite (not (= sy4_{id} (_ bv18446744073709551615 64))) (= sret4_{id} sret3_{id}) (= sret4_{id} (bvadd sret3_{id} (_ bv4 64)))))
(assert (ite (not (= sy4_{id} (_ bv18446744073709551615 64))) (= sx4_{id} sy4_{id}) (= sx4_{id} sx8_{id})))

; round 5
(declare-fun sret5_{id} () (_ BitVec 64))
(declare-fun sy2_{id} () (_ BitVec 64))
(declare-fun sx2_{id} () (_ BitVec 64))

(assert (= sy2_{id} (bvashr sx4_{id} #x0000000000000002)))
(assert (ite (not (= sy2_{id} (_ bv18446744073709551615 64))) (= sret5_{id} sret4_{id}) (= sret5_{id} (bvadd sret4_{id} (_ bv2 64)))))
(assert (ite (not (= sy2_{id} (_ bv18446744073709551615 64))) (= sx2_{id} sy2_{id}) (= sx2_{id} sx4_{id})))

; round 6
(declare-fun sret6_{id} () (_ BitVec 64))
(declare-fun sy1_{id} () (_ BitVec 64))
(declare-fun sx1_{id} () (_ BitVec 64))

(assert (= sy1_{id} (bvashr sx2_{id} #x0000000000000001)))
(assert (ite (not (= sy1_{id} (_ bv18446744073709551615 64))) (= sret6_{id} sret5_{id}) (= sret6_{id} (bvadd sret5_{id} (_ bv1 64)))))
(assert (ite (not (= sy1_{id} (_ bv18446744073709551615 64))) (= sx1_{id} sy1_{id}) (= sx1_{id} sx2_{id})))

; last round
(declare-fun sret7_{id} () (_ BitVec 64))
(assert (ite (not (= sx1_{id} (_ bv18446744073709551615 64))) (= sret7_{id} sret6_{id}) (= sret7_{id} (bvadd sret6_{id} (_ bv1 64)))))

(declare-fun clsret_{id} () (_ BitVec 64))
(assert (ite (= sret7_{id} (_ bv0 64)) (= clsret_{id} sret7_{id}) (= clsret_{id} (bvsub sret7_{id} (_ bv1 64)))))





(declare-fun cls64ret_{id} () (_ BitVec 64))
(assert (ite (bvsle (_ bv0 64) {x}) (= cls64ret_{id} clzret_{id}) (= cls64ret_{id} clsret_{id})))
