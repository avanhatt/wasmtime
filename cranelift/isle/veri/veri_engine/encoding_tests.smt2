(set-option :print-success true)
(set-option :produce-models true)
(declare-const input (_ BitVec 64))
(declare-const zret0_0 (_ BitVec 64))
(declare-const zret1_0 (_ BitVec 64))
(declare-const zy32_0 (_ BitVec 64))
(declare-const zx32_0 (_ BitVec 64))
(declare-const zret2_0 (_ BitVec 64))
(declare-const zy16_0 (_ BitVec 64))
(declare-const zx16_0 (_ BitVec 64))
(declare-const zret3_0 (_ BitVec 64))
(declare-const zy8_0 (_ BitVec 64))
(declare-const zx8_0 (_ BitVec 64))
(declare-const zret4_0 (_ BitVec 64))
(declare-const zy4_0 (_ BitVec 64))
(declare-const zx4_0 (_ BitVec 64))
(declare-const zret5_0 (_ BitVec 64))
(declare-const zy2_0 (_ BitVec 64))
(declare-const zx2_0 (_ BitVec 64))
(declare-const zret6_0 (_ BitVec 64))
(declare-const zy1_0 (_ BitVec 64))
(declare-const zx1_0 (_ BitVec 64))
(declare-const zret7_0 (_ BitVec 64))
(declare-const clzret_0 (_ BitVec 64))
(declare-const sret0_0 (_ BitVec 64))
(declare-const sret1_0 (_ BitVec 64))
(declare-const sy32_0 (_ BitVec 64))
(declare-const sx32_0 (_ BitVec 64))
(declare-const sret2_0 (_ BitVec 64))
(declare-const sy16_0 (_ BitVec 64))
(declare-const sx16_0 (_ BitVec 64))
(declare-const sret3_0 (_ BitVec 64))
(declare-const sy8_0 (_ BitVec 64))
(declare-const sx8_0 (_ BitVec 64))
(declare-const sret4_0 (_ BitVec 64))
(declare-const sy4_0 (_ BitVec 64))
(declare-const sx4_0 (_ BitVec 64))
(declare-const sret5_0 (_ BitVec 64))
(declare-const sy2_0 (_ BitVec 64))
(declare-const sx2_0 (_ BitVec 64))
(declare-const sret6_0 (_ BitVec 64))
(declare-const sy1_0 (_ BitVec 64))
(declare-const sx1_0 (_ BitVec 64))
(declare-const sret7_0 (_ BitVec 64))
(declare-const clsret_0 (_ BitVec 64))
(declare-const cls64ret_0 (_ BitVec 64))
(assert (and (= input #b1111111111111111111111111111111111111111111111111111111111111111) (= zret0_0 (_ bv0 64)) (= zy32_0 (bvlshr input #x0000000000000020)) (ite (not (= zy32_0 (_ bv0 64))) (= zret1_0 zret0_0) (= zret1_0 (bvadd zret0_0 (_ bv32 64)))) (ite (not (= zy32_0 (_ bv0 64))) (= zx32_0 zy32_0) (= zx32_0 input)) (= zy16_0 (bvlshr zx32_0 #x0000000000000010)) (ite (not (= zy16_0 (_ bv0 64))) (= zret2_0 zret1_0) (= zret2_0 (bvadd zret1_0 (_ bv16 64)))) (ite (not (= zy16_0 (_ bv0 64))) (= zx16_0 zy16_0) (= zx16_0 zx32_0)) (= zy8_0 (bvlshr zx16_0 #x0000000000000008)) (ite (not (= zy8_0 (_ bv0 64))) (= zret3_0 zret2_0) (= zret3_0 (bvadd zret2_0 (_ bv8 64)))) (ite (not (= zy8_0 (_ bv0 64))) (= zx8_0 zy8_0) (= zx8_0 zx16_0)) (= zy4_0 (bvlshr zx8_0 #x0000000000000004)) (ite (not (= zy4_0 (_ bv0 64))) (= zret4_0 zret3_0) (= zret4_0 (bvadd zret3_0 (_ bv4 64)))) (ite (not (= zy4_0 (_ bv0 64))) (= zx4_0 zy4_0) (= zx4_0 zx8_0)) (= zy2_0 (bvlshr zx4_0 #x0000000000000002)) (ite (not (= zy2_0 (_ bv0 64))) (= zret5_0 zret4_0) (= zret5_0 (bvadd zret4_0 (_ bv2 64)))) (ite (not (= zy2_0 (_ bv0 64))) (= zx2_0 zy2_0) (= zx2_0 zx4_0)) (= zy1_0 (bvlshr zx2_0 #x0000000000000001)) (ite (not (= zy1_0 (_ bv0 64))) (= zret6_0 zret5_0) (= zret6_0 (bvadd zret5_0 (_ bv1 64)))) (ite (not (= zy1_0 (_ bv0 64))) (= zx1_0 zy1_0) (= zx1_0 zx2_0)) (ite (not (= zx1_0 (_ bv0 64))) (= zret7_0 zret6_0) (= zret7_0 (bvadd zret6_0 (_ bv1 64)))) (ite (= zret7_0 (_ bv0 64)) (= clzret_0 zret7_0) (= clzret_0 (bvsub zret7_0 (_ bv1 64)))) (= sret0_0 (_ bv0 64)) (= sy32_0 (bvashr input #x0000000000000020)) (ite (not (= sy32_0 (_ bv18446744073709551615 64))) (= sret1_0 sret0_0) (= sret1_0 (bvadd sret0_0 (_ bv32 64)))) (ite (not (= sy32_0 (_ bv18446744073709551615 64))) (= sx32_0 sy32_0) (= sx32_0 input)) (= sy16_0 (bvashr sx32_0 #x0000000000000010)) (ite (not (= sy16_0 (_ bv18446744073709551615 64))) (= sret2_0 sret1_0) (= sret2_0 (bvadd sret1_0 (_ bv16 64)))) (ite (not (= sy16_0 (_ bv18446744073709551615 64))) (= sx16_0 sy16_0) (= sx16_0 sx32_0)) (= sy8_0 (bvashr sx16_0 #x0000000000000008)) (ite (not (= sy8_0 (_ bv18446744073709551615 64))) (= sret3_0 sret2_0) (= sret3_0 (bvadd sret2_0 (_ bv8 64)))) (ite (not (= sy8_0 (_ bv18446744073709551615 64))) (= sx8_0 sy8_0) (= sx8_0 sx16_0)) (= sy4_0 (bvashr sx8_0 #x0000000000000004)) (ite (not (= sy4_0 (_ bv18446744073709551615 64))) (= sret4_0 sret3_0) (= sret4_0 (bvadd sret3_0 (_ bv4 64)))) (ite (not (= sy4_0 (_ bv18446744073709551615 64))) (= sx4_0 sy4_0) (= sx4_0 sx8_0)) (= sy2_0 (bvashr sx4_0 #x0000000000000002)) (ite (not (= sy2_0 (_ bv18446744073709551615 64))) (= sret5_0 sret4_0) (= sret5_0 (bvadd sret4_0 (_ bv2 64)))) (ite (not (= sy2_0 (_ bv18446744073709551615 64))) (= sx2_0 sy2_0) (= sx2_0 sx4_0)) (= sy1_0 (bvashr sx2_0 #x0000000000000001)) (ite (not (= sy1_0 (_ bv18446744073709551615 64))) (= sret6_0 sret5_0) (= sret6_0 (bvadd sret5_0 (_ bv1 64)))) (ite (not (= sy1_0 (_ bv18446744073709551615 64))) (= sx1_0 sy1_0) (= sx1_0 sx2_0)) (ite (not (= sx1_0 (_ bv18446744073709551615 64))) (= sret7_0 sret6_0) (= sret7_0 (bvadd sret6_0 (_ bv1 64)))) (ite (= sret7_0 (_ bv0 64)) (= clsret_0 sret7_0) (= clsret_0 (bvsub sret7_0 (_ bv1 64)))) (ite (bvsle (_ bv0 64) input) (= cls64ret_0 clzret_0) (= cls64ret_0 clsret_0))))
(push)
(assert (= ((_ extract 63 0) cls64ret_0) #b0000000000000000000000000000000000000000000000000000000000111111))
(check-sat)
(pop)
(push)
(assert (not (= ((_ extract 63 0) cls64ret_0) #b0000000000000000000000000000000000000000000000000000000000111111)))
(check-sat)
(pop)
