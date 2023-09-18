; total zeros counter
(declare-fun ret1_{id} () (_ BitVec 16))
(assert (= ret1_{id} (_ bv0 16)))

; round 1
(declare-fun ret2_{id} () (_ BitVec 16))
(declare-fun y8_{id} () (_ BitVec 16))
(declare-fun x8_{id} () (_ BitVec 16))

(assert (= y8_{id} (bvlshr {x} #x0008)))
(assert (ite (not (= y8_{id} (_ bv0 16))) (= ret2_{id} ret1_{id}) (= ret2_{id} (bvadd ret1_{id} (_ bv8 16)))))
(assert (ite (not (= y8_{id} (_ bv0 16))) (= x8_{id} y8_{id}) (= x8_{id} {x})))

; round 2
(declare-fun ret3_{id} () (_ BitVec 16))
(declare-fun y4_{id} () (_ BitVec 16))
(declare-fun x4_{id} () (_ BitVec 16))

(assert (= y4_{id} (bvlshr x8_{id} #x0004)))
(assert (ite (not (= y4_{id} (_ bv0 16))) (= ret3_{id} ret2_{id}) (= ret3_{id} (bvadd ret2_{id} (_ bv4 16)))))
(assert (ite (not (= y4_{id} (_ bv0 16))) (= x4_{id} y4_{id}) (= x4_{id} x8_{id})))

; round 3
(declare-fun ret4_{id} () (_ BitVec 16))
(declare-fun y2_{id} () (_ BitVec 16))
(declare-fun x2_{id} () (_ BitVec 16))

(assert (= y2_{id} (bvlshr x4_{id} #x0002)))
(assert (ite (not (= y2_{id} (_ bv0 16))) (= ret4_{id} ret3_{id}) (= ret4_{id} (bvadd ret3_{id} (_ bv2 16)))))
(assert (ite (not (= y2_{id} (_ bv0 16))) (= x2_{id} y2_{id}) (= x2_{id} x4_{id})))

; round 4
(declare-fun ret5_{id} () (_ BitVec 16))
(declare-fun y1_{id} () (_ BitVec 16))
(declare-fun x1_{id} () (_ BitVec 16))

(assert (= y1_{id} (bvlshr x2_{id} #x0001)))
(assert (ite (not (= y1_{id} (_ bv0 16))) (= ret5_{id} ret4_{id}) (= ret5_{id} (bvadd ret4_{id} (_ bv1 16)))))
(assert (ite (not (= y1_{id} (_ bv0 16))) (= x1_{id} y1_{id}) (= x1_{id} x2_{id})))

; last round
(declare-fun ret6_{id} () (_ BitVec 16))
(assert (ite (not (= x1_{id} (_ bv0 16))) (= ret6_{id} ret5_{id}) (= ret6_{id} (bvadd ret5_{id} (_ bv1 16)))))