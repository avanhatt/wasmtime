; total zeros counter
(declare-fun ret0_{id} () (_ BitVec 8))
(assert (= ret0_{id} (_ bv0 8)))

; round 1
(declare-fun ret3_{id} () (_ BitVec 8))
(declare-fun y4_{id} () (_ BitVec 8))
(declare-fun x4_{id} () (_ BitVec 8))

(assert (= y4_{id} (bvlshr {x} #x04)))
(assert (ite (not (= y4_{id} (_ bv0 8))) (= ret3_{id} ret0_{id}) (= ret3_{id} (bvadd ret0_{id} (_ bv4 8)))))
(assert (ite (not (= y4_{id} (_ bv0 8))) (= x4_{id} y4_{id}) (= x4_{id} {x})))

; round 2
(declare-fun ret4_{id} () (_ BitVec 8))
(declare-fun y2_{id} () (_ BitVec 8))
(declare-fun x2_{id} () (_ BitVec 8))

(assert (= y2_{id} (bvlshr x4_{id} #x02)))
(assert (ite (not (= y2_{id} (_ bv0 8))) (= ret4_{id} ret3_{id}) (= ret4_{id} (bvadd ret3_{id} (_ bv2 8)))))
(assert (ite (not (= y2_{id} (_ bv0 8))) (= x2_{id} y2_{id}) (= x2_{id} x4_{id})))

; round 3
(declare-fun ret5_{id} () (_ BitVec 8))
(declare-fun y1_{id} () (_ BitVec 8))
(declare-fun x1_{id} () (_ BitVec 8))

(assert (= y1_{id} (bvlshr x2_{id} #x01)))
(assert (ite (not (= y1_{id} (_ bv0 8))) (= ret5_{id} ret4_{id}) (= ret5_{id} (bvadd ret4_{id} (_ bv1 8)))))
(assert (ite (not (= y1_{id} (_ bv0 8))) (= x1_{id} y1_{id}) (= x1_{id} x2_{id})))

; last round
(declare-fun ret6_{id} () (_ BitVec 8))
(assert (ite (not (= x1_{id} (_ bv0 8))) (= ret6_{id} ret5_{id}) (= ret6_{id} (bvadd ret5_{id} (_ bv1 8)))))
