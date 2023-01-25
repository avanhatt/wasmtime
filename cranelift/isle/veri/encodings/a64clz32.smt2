(declare-fun {x} () (_ BitVec 32))
(assert (= {x} (_ bv5 32))) ; placeholder to test x = 5

; extract to ensure we have a 32 bit input
(declare-fun a64x_{id} () (_ BitVec 32))
(assert (= a64x_{id} ((_ extract 31 0) {x})))

; total zeros counter
(declare-fun ret0_{id} () (_ BitVec 64))
(assert (= ret0_{id} (_ bv0 64)))

; round 1
(declare-fun ret2_{id} () (_ BitVec 64))
(declare-fun y16_{id} () (_ BitVec 32))
(declare-fun x16_{id} () (_ BitVec 32))

(assert (= y16_{id} (bvlshr a64x_{id} #x00000010)))
(assert (ite (not (= y16_{id} (_ bv0 32))) (= ret2_{id} ret0_{id}) (= ret2_{id} (bvadd ret0_{id} (_ bv16 64)))))
(assert (ite (not (= y16_{id} (_ bv0 32))) (= x16_{id} y16_{id}) (= x16_{id} a64x_{id})))

; round 2
(declare-fun ret3_{id} () (_ BitVec 64))
(declare-fun y8_{id} () (_ BitVec 32))
(declare-fun x8_{id} () (_ BitVec 32))

(assert (= y8_{id} (bvlshr x16_{id} #x00000008)))
(assert (ite (not (= y8_{id} (_ bv0 32))) (= ret3_{id} ret2_{id}) (= ret3_{id} (bvadd ret2_{id} (_ bv8 64)))))
(assert (ite (not (= y8_{id} (_ bv0 32))) (= x8_{id} y8_{id}) (= x8_{id} x16_{id})))

; round 3
(declare-fun ret4_{id} () (_ BitVec 64))
(declare-fun y4_{id} () (_ BitVec 32))
(declare-fun x4_{id} () (_ BitVec 32))

(assert (= y4_{id} (bvlshr x8_{id} #x00000004)))
(assert (ite (not (= y4_{id} (_ bv0 32))) (= ret4_{id} ret3_{id}) (= ret4_{id} (bvadd ret3_{id} (_ bv4 64)))))
(assert (ite (not (= y4_{id} (_ bv0 32))) (= x4_{id} y4_{id}) (= x4_{id} x8_{id})))

; round 4
(declare-fun ret5_{id} () (_ BitVec 64))
(declare-fun y2_{id} () (_ BitVec 32))
(declare-fun x2_{id} () (_ BitVec 32))

(assert (= y2_{id} (bvlshr x4_{id} #x00000002)))
(assert (ite (not (= y2_{id} (_ bv0 32))) (= ret5_{id} ret4_{id}) (= ret5_{id} (bvadd ret4_{id} (_ bv2 64)))))
(assert (ite (not (= y2_{id} (_ bv0 32))) (= x2_{id} y2_{id}) (= x2_{id} x4_{id})))

; round 5
(declare-fun ret6_{id} () (_ BitVec 64))
(declare-fun y1_{id} () (_ BitVec 32))
(declare-fun x1_{id} () (_ BitVec 32))

(assert (= y1_{id} (bvlshr x2_{id} #x00000001)))
(assert (ite (not (= y1_{id} (_ bv0 32))) (= ret6_{id} ret5_{id}) (= ret6_{id} (bvadd ret5_{id} (_ bv1 64)))))
(assert (ite (not (= y1_{id} (_ bv0 32))) (= x1_{id} y1_{id}) (= x1_{id} x2_{id})))

; last round
(declare-fun ret7_{id} () (_ BitVec 64))
(assert (ite (not (= x1_{id} (_ bv0 32))) (= ret7_{id} ret6_{id}) (= ret7_{id} (bvadd ret6_{id} (_ bv1 64)))))

(declare-fun clret_{id} () (_ BitVec 64))
(assert (ite (= ret7_{id} (_ bv0 64)) (= clret_{id} ret7_{id}) (= clret_{id} (bvsub ret7_{id} (_ bv1 64)))))
