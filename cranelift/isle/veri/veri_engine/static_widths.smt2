(set-option :print-success true)
(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(declare-const ScalarSize.Size32__9 Int)
(declare-const ScalarSize.Size32__9__result__41 Int)
(declare-const ScalarSize.Size8__19 Int)
(declare-const ScalarSize.Size8__19__result__138 Int)
(declare-const VectorSize.Size8x8__12 (_ BitVec 8))
(declare-const VectorSize.Size8x8__12__result__51 (_ BitVec 8))
(declare-const VectorSize.Size8x8__15 (_ BitVec 8))
(declare-const VectorSize.Size8x8__15__result__88 (_ BitVec 8))
(declare-const added__clif3__17 (_ BitVec 64))
(declare-const addv__16 (_ BitVec 64))
(declare-const addv__16__result__91 (_ BitVec 64))
(declare-const addv__16__s__92 (_ BitVec 8))
(declare-const addv__16__x__96 (_ BitVec 64))
(declare-const has_type__6 (_ BitVec 32))
(declare-const has_type__6__arg__28 (_ BitVec 32))
(declare-const has_type__6__result__27 (_ BitVec 32))
(declare-const has_type__6__ty__30 Int)
(declare-const let__22 (_ BitVec 32))
(declare-const lower__7 (_ BitVec 32))
(declare-const lower__7__arg__34 (_ BitVec 32))
(declare-const lower__7__result__33 (_ BitVec 32))
(declare-const mov_from_vec__20 (_ BitVec 64))
(declare-const mov_from_vec__20__i__145 (_ BitVec 8))
(declare-const mov_from_vec__20__result__141 (_ BitVec 64))
(declare-const mov_from_vec__20__s__142 Int)
(declare-const mov_from_vec__20__x__149 (_ BitVec 64))
(declare-const mov_to_fpu__10 (_ BitVec 64))
(declare-const mov_to_fpu__10__result__44 (_ BitVec 64))
(declare-const mov_to_fpu__10__s__46 Int)
(declare-const mov_to_fpu__10__x__47 (_ BitVec 64))
(declare-const nbits__clif2__14 (_ BitVec 64))
(declare-const output_reg__21 (_ BitVec 32))
(declare-const output_reg__21__arg__211 (_ BitVec 64))
(declare-const output_reg__21__result__209 (_ BitVec 32))
(declare-const popcnt__5 (_ BitVec 32))
(declare-const popcnt__5__result__23 (_ BitVec 32))
(declare-const popcnt__5__x__24 (_ BitVec 32))
(declare-const put_in_reg__8 (_ BitVec 64))
(declare-const put_in_reg__8__arg__38 (_ BitVec 32))
(declare-const put_in_reg__8__result__36 (_ BitVec 64))
(declare-const tmp__clif1__11 (_ BitVec 64))
(declare-const vec_cnt__13 (_ BitVec 64))
(declare-const vec_cnt__13__result__54 (_ BitVec 64))
(declare-const vec_cnt__13__s__55 (_ BitVec 8))
(declare-const vec_cnt__13__x__59 (_ BitVec 64))
(declare-const x__clif0__2 (_ BitVec 32))
(declare-const fresh0 (_ BitVec 32))
(declare-const popcnt_32_25 (_ BitVec 8))
(declare-const fresh1 (_ BitVec 32))
(declare-const popcnt_8_61 (_ BitVec 8))
(declare-const popcnt_8_63 (_ BitVec 8))
(declare-const popcnt_8_65 (_ BitVec 8))
(declare-const popcnt_8_67 (_ BitVec 8))
(declare-const popcnt_8_69 (_ BitVec 8))
(declare-const popcnt_8_71 (_ BitVec 8))
(declare-const popcnt_8_73 (_ BitVec 8))
(declare-const popcnt_8_75 (_ BitVec 8))
(push)
(assert (! (= x__clif0__2 fresh0) :named assum0))
(assert (! (= popcnt__5__result__23 ((_ zero_extend 24) popcnt_32_25)) :named assum1))
(assert (! (= x__clif0__2 popcnt__5__x__24) :named assum2))
(assert (! (= popcnt__5 popcnt__5__result__23) :named assum3))
(assert (! (= has_type__6__result__27 has_type__6__arg__28) :named assum4))
(assert (! (= has_type__6__ty__30 32) :named assum5))
(assert (! (= 32 has_type__6__ty__30) :named assum6))
(assert (! (= popcnt__5 has_type__6__arg__28) :named assum7))
(assert (! (= has_type__6 has_type__6__result__27) :named assum8))
(assert (! (= lower__7__result__33 lower__7__arg__34) :named assum9))
(assert (! (= has_type__6 lower__7__arg__34) :named assum10))
(assert (! (= lower__7 lower__7__result__33) :named assum11))
(assert (! (= put_in_reg__8__result__36 (concat fresh1 put_in_reg__8__arg__38)) :named assum12))
(assert (! (= x__clif0__2 put_in_reg__8__arg__38) :named assum13))
(assert (! (= put_in_reg__8 put_in_reg__8__result__36) :named assum14))
(assert (! (= ScalarSize.Size32__9__result__41 32) :named assum15))
(assert (! (= ScalarSize.Size32__9 ScalarSize.Size32__9__result__41) :named assum16))
(assert (! (= mov_to_fpu__10__result__44 ((_ zero_extend 32) ((_ extract 31 0) mov_to_fpu__10__x__47))) :named assum17))
(assert (! (= put_in_reg__8 mov_to_fpu__10__x__47) :named assum18))
(assert (! (= ScalarSize.Size32__9 mov_to_fpu__10__s__46) :named assum19))
(assert (! (= mov_to_fpu__10 mov_to_fpu__10__result__44) :named assum20))
(assert (! (= VectorSize.Size8x8__12__result__51 (_ bv0 8)) :named assum21))
(assert (! (= VectorSize.Size8x8__12 VectorSize.Size8x8__12__result__51) :named assum22))
(assert (! (= vec_cnt__13__result__54 (ite (= vec_cnt__13__s__55 (_ bv0 8)) (concat popcnt_8_61 (concat popcnt_8_63 (concat popcnt_8_65 (concat popcnt_8_67 (concat popcnt_8_69 (concat popcnt_8_71 (concat popcnt_8_73 popcnt_8_75))))))) (ite (= vec_cnt__13__s__55 (_ bv2 8)) vec_cnt__13__result__54 vec_cnt__13__result__54))) :named assum23))
(assert (! (= tmp__clif1__11 vec_cnt__13__x__59) :named assum24))
(assert (! (= VectorSize.Size8x8__12 vec_cnt__13__s__55) :named assum25))
(assert (! (= vec_cnt__13 vec_cnt__13__result__54) :named assum26))
(assert (! (= VectorSize.Size8x8__15__result__88 (_ bv0 8)) :named assum27))
(assert (! (= VectorSize.Size8x8__15 VectorSize.Size8x8__15__result__88) :named assum28))
(assert (! (= addv__16__result__91 (ite (= addv__16__s__92 (_ bv0 8)) ((_ zero_extend 56) (bvadd ((_ extract 7 0) addv__16__x__96) (bvadd ((_ extract 15 8) addv__16__x__96) (bvadd ((_ extract 23 16) addv__16__x__96) (bvadd ((_ extract 31 24) addv__16__x__96) (bvadd ((_ extract 39 32) addv__16__x__96) (bvadd ((_ extract 47 40) addv__16__x__96) (bvadd ((_ extract 55 48) addv__16__x__96) ((_ extract 63 56) addv__16__x__96))))))))) (ite (= addv__16__s__92 (_ bv1 8)) ((_ zero_extend 48) (bvadd ((_ extract 15 0) addv__16__x__96) (bvadd ((_ extract 31 16) addv__16__x__96) (bvadd ((_ extract 47 32) addv__16__x__96) ((_ extract 63 48) addv__16__x__96))))) ((_ zero_extend 32) (bvadd ((_ extract 31 0) addv__16__x__96) ((_ extract 63 32) addv__16__x__96)))))) :named assum29))
(assert (! (= nbits__clif2__14 addv__16__x__96) :named assum30))
(assert (! (= VectorSize.Size8x8__15 addv__16__s__92) :named assum31))
(assert (! (= addv__16 addv__16__result__91) :named assum32))
(assert (! (= ScalarSize.Size8__19__result__138 8) :named assum33))
(assert (! (= ScalarSize.Size8__19 ScalarSize.Size8__19__result__138) :named assum34))
(assert (! (= mov_from_vec__20__result__141 (ite (= mov_from_vec__20__s__142 8) (ite (= mov_from_vec__20__i__145 (_ bv0 8)) ((_ zero_extend 56) ((_ extract 7 0) mov_from_vec__20__x__149)) (ite (= mov_from_vec__20__i__145 (_ bv1 8)) ((_ zero_extend 56) ((_ extract 15 8) mov_from_vec__20__x__149)) (ite (= mov_from_vec__20__i__145 (_ bv2 8)) ((_ zero_extend 56) ((_ extract 23 16) mov_from_vec__20__x__149)) (ite (= mov_from_vec__20__i__145 (_ bv3 8)) ((_ zero_extend 56) ((_ extract 31 24) mov_from_vec__20__x__149)) (ite (= mov_from_vec__20__i__145 (_ bv4 8)) ((_ zero_extend 56) ((_ extract 39 32) mov_from_vec__20__x__149)) (ite (= mov_from_vec__20__i__145 (_ bv5 8)) ((_ zero_extend 56) ((_ extract 47 40) mov_from_vec__20__x__149)) (ite (= mov_from_vec__20__i__145 (_ bv6 8)) ((_ zero_extend 56) ((_ extract 55 48) mov_from_vec__20__x__149)) ((_ zero_extend 56) ((_ extract 63 56) mov_from_vec__20__x__149))))))))) (ite (= mov_from_vec__20__s__142 16) (ite (= mov_from_vec__20__i__145 (_ bv0 8)) ((_ zero_extend 48) ((_ extract 15 0) mov_from_vec__20__x__149)) (ite (= mov_from_vec__20__i__145 (_ bv1 8)) ((_ zero_extend 48) ((_ extract 31 16) mov_from_vec__20__x__149)) (ite (= mov_from_vec__20__i__145 (_ bv3 8)) ((_ zero_extend 48) ((_ extract 47 32) mov_from_vec__20__x__149)) ((_ zero_extend 48) ((_ extract 63 48) mov_from_vec__20__x__149))))) (ite (= mov_from_vec__20__i__145 (_ bv0 8)) ((_ zero_extend 32) ((_ extract 31 0) mov_from_vec__20__x__149)) ((_ zero_extend 32) ((_ extract 63 32) mov_from_vec__20__x__149)))))) :named assum35))
(assert (! (= added__clif3__17 mov_from_vec__20__x__149) :named assum36))
(assert (! (= (_ bv0 8) mov_from_vec__20__i__145) :named assum37))
(assert (! (= ScalarSize.Size8__19 mov_from_vec__20__s__142) :named assum38))
(assert (! (= mov_from_vec__20 mov_from_vec__20__result__141) :named assum39))
(assert (! (= output_reg__21__result__209 ((_ extract 31 0) output_reg__21__arg__211)) :named assum40))
(assert (! (= mov_from_vec__20 output_reg__21__arg__211) :named assum41))
(assert (! (= output_reg__21 output_reg__21__result__209) :named assum42))
(assert (! (= tmp__clif1__11 mov_to_fpu__10) :named assum43))
(assert (! (= nbits__clif2__14 vec_cnt__13) :named assum44))
(assert (! (= added__clif3__17 addv__16) :named assum45))
(assert (! (= popcnt_32_25 (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd ((_ zero_extend 7) ((_ extract 31 31) popcnt__5__x__24)) ((_ zero_extend 7) ((_ extract 0 0) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 1 1) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 2 2) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 3 3) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 4 4) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 5 5) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 6 6) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 7 7) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 8 8) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 9 9) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 10 10) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 11 11) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 12 12) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 13 13) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 14 14) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 15 15) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 16 16) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 17 17) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 18 18) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 19 19) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 20 20) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 21 21) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 22 22) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 23 23) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 24 24) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 25 25) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 26 26) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 27 27) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 28 28) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 29 29) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 30 30) popcnt__5__x__24)))) :named assum46))
(assert (! (= popcnt_8_61 (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd ((_ zero_extend 7) ((_ extract 7 7) ((_ extract 63 56) vec_cnt__13__x__59))) ((_ zero_extend 7) ((_ extract 0 0) ((_ extract 63 56) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 1 1) ((_ extract 63 56) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 2 2) ((_ extract 63 56) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 3 3) ((_ extract 63 56) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 4 4) ((_ extract 63 56) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 5 5) ((_ extract 63 56) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 6 6) ((_ extract 63 56) vec_cnt__13__x__59))))) :named assum47))
(assert (! (= popcnt_8_63 (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd ((_ zero_extend 7) ((_ extract 7 7) ((_ extract 55 48) vec_cnt__13__x__59))) ((_ zero_extend 7) ((_ extract 0 0) ((_ extract 55 48) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 1 1) ((_ extract 55 48) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 2 2) ((_ extract 55 48) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 3 3) ((_ extract 55 48) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 4 4) ((_ extract 55 48) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 5 5) ((_ extract 55 48) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 6 6) ((_ extract 55 48) vec_cnt__13__x__59))))) :named assum48))
(assert (! (= popcnt_8_65 (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd ((_ zero_extend 7) ((_ extract 7 7) ((_ extract 47 40) vec_cnt__13__x__59))) ((_ zero_extend 7) ((_ extract 0 0) ((_ extract 47 40) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 1 1) ((_ extract 47 40) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 2 2) ((_ extract 47 40) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 3 3) ((_ extract 47 40) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 4 4) ((_ extract 47 40) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 5 5) ((_ extract 47 40) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 6 6) ((_ extract 47 40) vec_cnt__13__x__59))))) :named assum49))
(assert (! (= popcnt_8_67 (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd ((_ zero_extend 7) ((_ extract 7 7) ((_ extract 39 32) vec_cnt__13__x__59))) ((_ zero_extend 7) ((_ extract 0 0) ((_ extract 39 32) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 1 1) ((_ extract 39 32) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 2 2) ((_ extract 39 32) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 3 3) ((_ extract 39 32) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 4 4) ((_ extract 39 32) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 5 5) ((_ extract 39 32) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 6 6) ((_ extract 39 32) vec_cnt__13__x__59))))) :named assum50))
(assert (! (= popcnt_8_69 (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd ((_ zero_extend 7) ((_ extract 7 7) ((_ extract 31 24) vec_cnt__13__x__59))) ((_ zero_extend 7) ((_ extract 0 0) ((_ extract 31 24) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 1 1) ((_ extract 31 24) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 2 2) ((_ extract 31 24) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 3 3) ((_ extract 31 24) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 4 4) ((_ extract 31 24) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 5 5) ((_ extract 31 24) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 6 6) ((_ extract 31 24) vec_cnt__13__x__59))))) :named assum51))
(assert (! (= popcnt_8_71 (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd ((_ zero_extend 7) ((_ extract 7 7) ((_ extract 23 16) vec_cnt__13__x__59))) ((_ zero_extend 7) ((_ extract 0 0) ((_ extract 23 16) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 1 1) ((_ extract 23 16) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 2 2) ((_ extract 23 16) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 3 3) ((_ extract 23 16) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 4 4) ((_ extract 23 16) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 5 5) ((_ extract 23 16) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 6 6) ((_ extract 23 16) vec_cnt__13__x__59))))) :named assum52))
(assert (! (= popcnt_8_73 (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd ((_ zero_extend 7) ((_ extract 7 7) ((_ extract 15 8) vec_cnt__13__x__59))) ((_ zero_extend 7) ((_ extract 0 0) ((_ extract 15 8) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 1 1) ((_ extract 15 8) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 2 2) ((_ extract 15 8) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 3 3) ((_ extract 15 8) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 4 4) ((_ extract 15 8) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 5 5) ((_ extract 15 8) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 6 6) ((_ extract 15 8) vec_cnt__13__x__59))))) :named assum53))
(assert (! (= popcnt_8_75 (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd ((_ zero_extend 7) ((_ extract 7 7) ((_ extract 7 0) vec_cnt__13__x__59))) ((_ zero_extend 7) ((_ extract 0 0) ((_ extract 7 0) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 1 1) ((_ extract 7 0) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 2 2) ((_ extract 7 0) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 3 3) ((_ extract 7 0) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 4 4) ((_ extract 7 0) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 5 5) ((_ extract 7 0) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 6 6) ((_ extract 7 0) vec_cnt__13__x__59))))) :named assum54))
(check-sat)
(get-value (x__clif0__2))
(assert (not (= x__clif0__2 #x18d30000)))
(check-sat)
(pop)
(assert (not (=> (and (= x__clif0__2 fresh0) (= popcnt__5__result__23 ((_ zero_extend 24) popcnt_32_25)) (= x__clif0__2 popcnt__5__x__24) (= popcnt__5 popcnt__5__result__23) (= has_type__6__result__27 has_type__6__arg__28) (= has_type__6__ty__30 32) (= 32 has_type__6__ty__30) (= popcnt__5 has_type__6__arg__28) (= has_type__6 has_type__6__result__27) (= lower__7__result__33 lower__7__arg__34) (= has_type__6 lower__7__arg__34) (= lower__7 lower__7__result__33) (= put_in_reg__8__result__36 (concat fresh1 put_in_reg__8__arg__38)) (= x__clif0__2 put_in_reg__8__arg__38) (= put_in_reg__8 put_in_reg__8__result__36) (= ScalarSize.Size32__9__result__41 32) (= ScalarSize.Size32__9 ScalarSize.Size32__9__result__41) (= mov_to_fpu__10__result__44 ((_ zero_extend 32) ((_ extract 31 0) mov_to_fpu__10__x__47))) (= put_in_reg__8 mov_to_fpu__10__x__47) (= ScalarSize.Size32__9 mov_to_fpu__10__s__46) (= mov_to_fpu__10 mov_to_fpu__10__result__44) (= VectorSize.Size8x8__12__result__51 (_ bv0 8)) (= VectorSize.Size8x8__12 VectorSize.Size8x8__12__result__51) (= vec_cnt__13__result__54 (ite (= vec_cnt__13__s__55 (_ bv0 8)) (concat popcnt_8_61 (concat popcnt_8_63 (concat popcnt_8_65 (concat popcnt_8_67 (concat popcnt_8_69 (concat popcnt_8_71 (concat popcnt_8_73 popcnt_8_75))))))) (ite (= vec_cnt__13__s__55 (_ bv2 8)) vec_cnt__13__result__54 vec_cnt__13__result__54))) (= tmp__clif1__11 vec_cnt__13__x__59) (= VectorSize.Size8x8__12 vec_cnt__13__s__55) (= vec_cnt__13 vec_cnt__13__result__54) (= VectorSize.Size8x8__15__result__88 (_ bv0 8)) (= VectorSize.Size8x8__15 VectorSize.Size8x8__15__result__88) (= addv__16__result__91 (ite (= addv__16__s__92 (_ bv0 8)) ((_ zero_extend 56) (bvadd ((_ extract 7 0) addv__16__x__96) (bvadd ((_ extract 15 8) addv__16__x__96) (bvadd ((_ extract 23 16) addv__16__x__96) (bvadd ((_ extract 31 24) addv__16__x__96) (bvadd ((_ extract 39 32) addv__16__x__96) (bvadd ((_ extract 47 40) addv__16__x__96) (bvadd ((_ extract 55 48) addv__16__x__96) ((_ extract 63 56) addv__16__x__96))))))))) (ite (= addv__16__s__92 (_ bv1 8)) ((_ zero_extend 48) (bvadd ((_ extract 15 0) addv__16__x__96) (bvadd ((_ extract 31 16) addv__16__x__96) (bvadd ((_ extract 47 32) addv__16__x__96) ((_ extract 63 48) addv__16__x__96))))) ((_ zero_extend 32) (bvadd ((_ extract 31 0) addv__16__x__96) ((_ extract 63 32) addv__16__x__96)))))) (= nbits__clif2__14 addv__16__x__96) (= VectorSize.Size8x8__15 addv__16__s__92) (= addv__16 addv__16__result__91) (= ScalarSize.Size8__19__result__138 8) (= ScalarSize.Size8__19 ScalarSize.Size8__19__result__138) (= mov_from_vec__20__result__141 (ite (= mov_from_vec__20__s__142 8) (ite (= mov_from_vec__20__i__145 (_ bv0 8)) ((_ zero_extend 56) ((_ extract 7 0) mov_from_vec__20__x__149)) (ite (= mov_from_vec__20__i__145 (_ bv1 8)) ((_ zero_extend 56) ((_ extract 15 8) mov_from_vec__20__x__149)) (ite (= mov_from_vec__20__i__145 (_ bv2 8)) ((_ zero_extend 56) ((_ extract 23 16) mov_from_vec__20__x__149)) (ite (= mov_from_vec__20__i__145 (_ bv3 8)) ((_ zero_extend 56) ((_ extract 31 24) mov_from_vec__20__x__149)) (ite (= mov_from_vec__20__i__145 (_ bv4 8)) ((_ zero_extend 56) ((_ extract 39 32) mov_from_vec__20__x__149)) (ite (= mov_from_vec__20__i__145 (_ bv5 8)) ((_ zero_extend 56) ((_ extract 47 40) mov_from_vec__20__x__149)) (ite (= mov_from_vec__20__i__145 (_ bv6 8)) ((_ zero_extend 56) ((_ extract 55 48) mov_from_vec__20__x__149)) ((_ zero_extend 56) ((_ extract 63 56) mov_from_vec__20__x__149))))))))) (ite (= mov_from_vec__20__s__142 16) (ite (= mov_from_vec__20__i__145 (_ bv0 8)) ((_ zero_extend 48) ((_ extract 15 0) mov_from_vec__20__x__149)) (ite (= mov_from_vec__20__i__145 (_ bv1 8)) ((_ zero_extend 48) ((_ extract 31 16) mov_from_vec__20__x__149)) (ite (= mov_from_vec__20__i__145 (_ bv3 8)) ((_ zero_extend 48) ((_ extract 47 32) mov_from_vec__20__x__149)) ((_ zero_extend 48) ((_ extract 63 48) mov_from_vec__20__x__149))))) (ite (= mov_from_vec__20__i__145 (_ bv0 8)) ((_ zero_extend 32) ((_ extract 31 0) mov_from_vec__20__x__149)) ((_ zero_extend 32) ((_ extract 63 32) mov_from_vec__20__x__149)))))) (= added__clif3__17 mov_from_vec__20__x__149) (= (_ bv0 8) mov_from_vec__20__i__145) (= ScalarSize.Size8__19 mov_from_vec__20__s__142) (= mov_from_vec__20 mov_from_vec__20__result__141) (= output_reg__21__result__209 ((_ extract 31 0) output_reg__21__arg__211)) (= mov_from_vec__20 output_reg__21__arg__211) (= output_reg__21 output_reg__21__result__209) (= tmp__clif1__11 mov_to_fpu__10) (= nbits__clif2__14 vec_cnt__13) (= added__clif3__17 addv__16) (= popcnt_32_25 (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd ((_ zero_extend 7) ((_ extract 31 31) popcnt__5__x__24)) ((_ zero_extend 7) ((_ extract 0 0) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 1 1) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 2 2) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 3 3) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 4 4) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 5 5) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 6 6) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 7 7) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 8 8) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 9 9) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 10 10) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 11 11) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 12 12) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 13 13) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 14 14) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 15 15) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 16 16) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 17 17) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 18 18) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 19 19) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 20 20) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 21 21) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 22 22) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 23 23) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 24 24) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 25 25) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 26 26) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 27 27) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 28 28) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 29 29) popcnt__5__x__24))) ((_ zero_extend 7) ((_ extract 30 30) popcnt__5__x__24)))) (= popcnt_8_61 (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd ((_ zero_extend 7) ((_ extract 7 7) ((_ extract 63 56) vec_cnt__13__x__59))) ((_ zero_extend 7) ((_ extract 0 0) ((_ extract 63 56) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 1 1) ((_ extract 63 56) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 2 2) ((_ extract 63 56) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 3 3) ((_ extract 63 56) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 4 4) ((_ extract 63 56) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 5 5) ((_ extract 63 56) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 6 6) ((_ extract 63 56) vec_cnt__13__x__59))))) (= popcnt_8_63 (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd ((_ zero_extend 7) ((_ extract 7 7) ((_ extract 55 48) vec_cnt__13__x__59))) ((_ zero_extend 7) ((_ extract 0 0) ((_ extract 55 48) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 1 1) ((_ extract 55 48) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 2 2) ((_ extract 55 48) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 3 3) ((_ extract 55 48) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 4 4) ((_ extract 55 48) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 5 5) ((_ extract 55 48) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 6 6) ((_ extract 55 48) vec_cnt__13__x__59))))) (= popcnt_8_65 (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd ((_ zero_extend 7) ((_ extract 7 7) ((_ extract 47 40) vec_cnt__13__x__59))) ((_ zero_extend 7) ((_ extract 0 0) ((_ extract 47 40) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 1 1) ((_ extract 47 40) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 2 2) ((_ extract 47 40) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 3 3) ((_ extract 47 40) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 4 4) ((_ extract 47 40) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 5 5) ((_ extract 47 40) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 6 6) ((_ extract 47 40) vec_cnt__13__x__59))))) (= popcnt_8_67 (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd ((_ zero_extend 7) ((_ extract 7 7) ((_ extract 39 32) vec_cnt__13__x__59))) ((_ zero_extend 7) ((_ extract 0 0) ((_ extract 39 32) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 1 1) ((_ extract 39 32) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 2 2) ((_ extract 39 32) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 3 3) ((_ extract 39 32) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 4 4) ((_ extract 39 32) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 5 5) ((_ extract 39 32) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 6 6) ((_ extract 39 32) vec_cnt__13__x__59))))) (= popcnt_8_69 (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd ((_ zero_extend 7) ((_ extract 7 7) ((_ extract 31 24) vec_cnt__13__x__59))) ((_ zero_extend 7) ((_ extract 0 0) ((_ extract 31 24) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 1 1) ((_ extract 31 24) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 2 2) ((_ extract 31 24) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 3 3) ((_ extract 31 24) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 4 4) ((_ extract 31 24) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 5 5) ((_ extract 31 24) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 6 6) ((_ extract 31 24) vec_cnt__13__x__59))))) (= popcnt_8_71 (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd ((_ zero_extend 7) ((_ extract 7 7) ((_ extract 23 16) vec_cnt__13__x__59))) ((_ zero_extend 7) ((_ extract 0 0) ((_ extract 23 16) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 1 1) ((_ extract 23 16) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 2 2) ((_ extract 23 16) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 3 3) ((_ extract 23 16) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 4 4) ((_ extract 23 16) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 5 5) ((_ extract 23 16) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 6 6) ((_ extract 23 16) vec_cnt__13__x__59))))) (= popcnt_8_73 (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd ((_ zero_extend 7) ((_ extract 7 7) ((_ extract 15 8) vec_cnt__13__x__59))) ((_ zero_extend 7) ((_ extract 0 0) ((_ extract 15 8) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 1 1) ((_ extract 15 8) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 2 2) ((_ extract 15 8) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 3 3) ((_ extract 15 8) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 4 4) ((_ extract 15 8) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 5 5) ((_ extract 15 8) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 6 6) ((_ extract 15 8) vec_cnt__13__x__59))))) (= popcnt_8_75 (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd ((_ zero_extend 7) ((_ extract 7 7) ((_ extract 7 0) vec_cnt__13__x__59))) ((_ zero_extend 7) ((_ extract 0 0) ((_ extract 7 0) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 1 1) ((_ extract 7 0) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 2 2) ((_ extract 7 0) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 3 3) ((_ extract 7 0) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 4 4) ((_ extract 7 0) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 5 5) ((_ extract 7 0) vec_cnt__13__x__59)))) ((_ zero_extend 7) ((_ extract 6 6) ((_ extract 7 0) vec_cnt__13__x__59)))))) (and (= ((_ extract 31 0) lower__7) ((_ extract 31 0) output_reg__21)) (and (or (= vec_cnt__13__s__55 (_ bv0 8)) (or (= vec_cnt__13__s__55 (_ bv2 8)) (= vec_cnt__13__s__55 (_ bv4 8)))) (or (= addv__16__s__92 (_ bv0 8)) (or (= addv__16__s__92 (_ bv1 8)) (= addv__16__s__92 (_ bv2 8)))) (or (= vec_cnt__13__s__55 (_ bv0 8)) (= vec_cnt__13__s__55 (_ bv2 8)) (= vec_cnt__13__s__55 (_ bv4 8))) (or (= addv__16__s__92 (_ bv0 8)) (= addv__16__s__92 (_ bv1 8)) (= addv__16__s__92 (_ bv2 8))) (or (= mov_from_vec__20__i__145 (_ bv0 8)) (= mov_from_vec__20__i__145 (_ bv1 8)) (= mov_from_vec__20__i__145 (_ bv2 8)) (= mov_from_vec__20__i__145 (_ bv3 8)) (= mov_from_vec__20__i__145 (_ bv4 8)) (= mov_from_vec__20__i__145 (_ bv5 8)) (= mov_from_vec__20__i__145 (_ bv6 8)) (= mov_from_vec__20__i__145 (_ bv7 8))) (or (= mov_from_vec__20__i__145 (_ bv0 8)) (= mov_from_vec__20__i__145 (_ bv1 8)) (= mov_from_vec__20__i__145 (_ bv3 8)) (= mov_from_vec__20__i__145 (_ bv4 8))) (or (= mov_from_vec__20__i__145 (_ bv0 8)) (= mov_from_vec__20__i__145 (_ bv1 8))) (or (= mov_from_vec__20__s__142 8) (= mov_from_vec__20__s__142 16) (= mov_from_vec__20__s__142 32)))))))
(check-sat)
