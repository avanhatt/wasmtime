(set-option :print-success true)
(set-option :produce-models true)
(declare-const x (_ BitVec 64))
(declare-const y (_ BitVec 64))

(require(not (= (bvsub x y) (bvadd x (bvadd (bvnot y) #x0000000000000001)))))

(check-sat)