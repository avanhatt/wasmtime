; total zeros counter
(declare-fun ret0_{id} () (_ BitVec 64))
(assert (= ret0_{id} (_ bv0 64)))

; round 1
(declare-fun ret1_{id} () (_ BitVec 64))
(declare-fun y32_{id} () (_ BitVec 64))
(declare-fun x32_{id} () (_ BitVec 64))

(assert (= y32_{id} (bvlshr {x} #x0000000000000020)))
(assert (ite (not (= y32_{id} (_ bv0 64))) (= ret1_{id} ret0_{id}) (= ret1_{id} (bvadd ret0_{id} (_ bv32 64)))))
(assert (ite (not (= y32_{id} (_ bv0 64))) (= x32_{id} y32_{id}) (= x32_{id} {x})))

; round 2
(declare-fun ret2_{id} () (_ BitVec 64))
(declare-fun y16_{id} () (_ BitVec 64))
(declare-fun x16_{id} () (_ BitVec 64))

(assert (= y16_{id} (bvlshr x32_{id} #x0000000000000010)))
(assert (ite (not (= y16_{id} (_ bv0 64))) (= ret2_{id} ret1_{id}) (= ret2_{id} (bvadd ret1_{id} (_ bv16 64)))))
(assert (ite (not (= y16_{id} (_ bv0 64))) (= x16_{id} y16_{id}) (= x16_{id} x32_{id})))

; round 3
(declare-fun ret3_{id} () (_ BitVec 64))
(declare-fun y8_{id} () (_ BitVec 64))
(declare-fun x8_{id} () (_ BitVec 64))

(assert (= y8_{id} (bvlshr x16_{id} #x0000000000000008)))
(assert (ite (not (= y8_{id} (_ bv0 64))) (= ret3_{id} ret2_{id}) (= ret3_{id} (bvadd ret2_{id} (_ bv8 64)))))
(assert (ite (not (= y8_{id} (_ bv0 64))) (= x8_{id} y8_{id}) (= x8_{id} x16_{id})))

; round 4
(declare-fun ret4_{id} () (_ BitVec 64))
(declare-fun y4_{id} () (_ BitVec 64))
(declare-fun x4_{id} () (_ BitVec 64))

(assert (= y4_{id} (bvlshr x8_{id} #x0000000000000004)))
(assert (ite (not (= y4_{id} (_ bv0 64))) (= ret4_{id} ret3_{id}) (= ret4_{id} (bvadd ret3_{id} (_ bv4 64)))))
(assert (ite (not (= y4_{id} (_ bv0 64))) (= x4_{id} y4_{id}) (= x4_{id} x8_{id})))

; round 5
(declare-fun ret5_{id} () (_ BitVec 64))
(declare-fun y2_{id} () (_ BitVec 64))
(declare-fun x2_{id} () (_ BitVec 64))

(assert (= y2_{id} (bvlshr x4_{id} #x0000000000000002)))
(assert (ite (not (= y2_{id} (_ bv0 64))) (= ret5_{id} ret4_{id}) (= ret5_{id} (bvadd ret4_{id} (_ bv2 64)))))
(assert (ite (not (= y2_{id} (_ bv0 64))) (= x2_{id} y2_{id}) (= x2_{id} x4_{id})))

; round 6
(declare-fun ret6_{id} () (_ BitVec 64))
(declare-fun y1_{id} () (_ BitVec 64))
(declare-fun x1_{id} () (_ BitVec 64))

(assert (= y1_{id} (bvlshr x2_{id} #x0000000000000001)))
(assert (ite (not (= y1_{id} (_ bv0 64))) (= ret6_{id} ret5_{id}) (= ret6_{id} (bvadd ret5_{id} (_ bv1 64)))))
(assert (ite (not (= y1_{id} (_ bv0 64))) (= x1_{id} y1_{id}) (= x1_{id} x2_{id})))
