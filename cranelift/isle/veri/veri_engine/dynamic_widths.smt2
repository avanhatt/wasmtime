(set-option :print-success true)
(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(declare-const bnot__8 (_ BitVec 8))
(declare-const bnot__8__result__35 (_ BitVec 8))
(declare-const bnot__8__x__19 (_ BitVec 8))
(declare-const fits_in_64__4 Int)
(declare-const fits_in_64__4__arg__15 Int)
(declare-const fits_in_64__4__result__17 Int)
(declare-const has_type__9 (_ BitVec 64))
(declare-const has_type__9__arg__39 (_ BitVec 8))
(declare-const has_type__9__result__40 (_ BitVec 64))
(declare-const has_type__9__ty__37 Int)
(declare-const lower__10 (_ BitVec 64))
(declare-const lower__10__arg__44 (_ BitVec 64))
(declare-const lower__10__result__42 (_ BitVec 64))
(declare-const orr_not__13 (_ BitVec 64))
(declare-const orr_not__13__a__53 (_ BitVec 64))
(declare-const orr_not__13__b__54 (_ BitVec 64))
(declare-const orr_not__13__result__50 (_ BitVec 64))
(declare-const orr_not__13__ty__52 Int)
(declare-const output_reg__14 (_ BitVec 64))
(declare-const output_reg__14__arg__57 (_ BitVec 64))
(declare-const output_reg__14__result__55 (_ BitVec 64))
(declare-const put_in_reg__12 (_ BitVec 64))
(declare-const put_in_reg__12__arg__49 (_ BitVec 8))
(declare-const put_in_reg__12__result__47 (_ BitVec 64))
(declare-const ty__clif0__1 Int)
(declare-const x__clif1__5 (_ BitVec 8))
(declare-const zero_reg__11 (_ BitVec 64))
(declare-const zero_reg__11__result__45 (_ BitVec 64))
(declare-const width__11 Int)
(declare-const width__49 Int)
(declare-const width__57 Int)
(declare-const width__40 Int)
(declare-const width__10 Int)
(declare-const width__47 Int)
(declare-const width__9 Int)
(declare-const width__50 Int)
(declare-const width__55 Int)
(declare-const width__44 Int)
(declare-const width__12 Int)
(declare-const width__19 Int)
(declare-const width__6 Int)
(declare-const width__13 Int)
(declare-const width__5 Int)
(declare-const width__14 Int)
(declare-const width__53 Int)
(declare-const width__42 Int)
(declare-const width__45 Int)
(declare-const width__35 Int)
(declare-const width__8 Int)
(declare-const width__54 Int)
(declare-const width__39 Int)
(declare-const bnot__8_narrow__8 (_ BitVec 8))
(declare-const bnot__8_wide__8 (_ BitVec 64))
(declare-const fresh0 (_ BitVec 56))
(declare-const bnot__8__result__35_narrow__35 (_ BitVec 8))
(declare-const bnot__8__result__35_wide__35 (_ BitVec 64))
(declare-const fresh1 (_ BitVec 56))
(declare-const bnot__8__x__19_narrow__19 (_ BitVec 8))
(declare-const bnot__8__x__19_wide__19 (_ BitVec 64))
(declare-const fresh2 (_ BitVec 56))
(declare-const has_type__9__arg__39_narrow__39 (_ BitVec 8))
(declare-const has_type__9__arg__39_wide__39 (_ BitVec 64))
(declare-const fresh3 (_ BitVec 56))
(declare-const put_in_reg__12__arg__49_narrow__49 (_ BitVec 8))
(declare-const put_in_reg__12__arg__49_wide__49 (_ BitVec 64))
(declare-const fresh4 (_ BitVec 56))
(declare-const x__clif1__5_narrow__5 (_ BitVec 8))
(declare-const x__clif1__5_wide__5 (_ BitVec 64))
(declare-const fresh5 (_ BitVec 56))
(declare-const fresh6 Int)
(declare-const fresh7 (_ BitVec 64))
(push)
(assert (! (= ty__clif0__1 fresh6) :named dyn0))
(assert (! (<= fits_in_64__4__arg__15 fits_in_64__4__arg__15) :named dyn1))
(assert (! (= fits_in_64__4__result__17 fits_in_64__4__result__17) :named dyn2))
(assert (! (= ty__clif0__1 fits_in_64__4__arg__15) :named dyn3))
(assert (! (= fits_in_64__4 fits_in_64__4__result__17) :named dyn4))
(assert (! (= x__clif1__5_wide__5 fresh7) :named dyn5))
(assert (! (or (or (or (= width__19 width__19) (= width__19 width__19)) (= width__19 width__19)) (= width__19 width__19)) :named dyn6))
(assert (! (= bnot__8__result__35_wide__35 bnot__8__result__35_wide__35) :named dyn7))
(assert (! (= x__clif1__5_wide__5 bnot__8__x__19_wide__19) :named dyn8))
(assert (! (= bnot__8_wide__8 bnot__8__result__35_wide__35) :named dyn9))
(assert (! (= has_type__9__ty__37 has_type__9__ty__37) :named dyn10))
(assert (! (= has_type__9__result__40 has_type__9__result__40) :named dyn11))
(assert (! (= fits_in_64__4 has_type__9__ty__37) :named dyn12))
(assert (! (= bnot__8_wide__8 has_type__9__arg__39_wide__39) :named dyn13))
(assert (! (= has_type__9 has_type__9__result__40) :named dyn14))
(assert (! (= lower__10__result__42 lower__10__result__42) :named dyn15))
(assert (! (= has_type__9 lower__10__arg__44) :named dyn16))
(assert (! (= lower__10 lower__10__result__42) :named dyn17))
(assert (! (= zero_reg__11 zero_reg__11__result__45) :named dyn18))
(assert (! (= x__clif1__5_wide__5 put_in_reg__12__arg__49_wide__49) :named dyn19))
(assert (! (= put_in_reg__12 put_in_reg__12__result__47) :named dyn20))
(assert (! (= ty__clif0__1 orr_not__13__ty__52) :named dyn21))
(assert (! (= zero_reg__11 orr_not__13__a__53) :named dyn22))
(assert (! (= put_in_reg__12 orr_not__13__b__54) :named dyn23))
(assert (! (= orr_not__13 orr_not__13__result__50) :named dyn24))
(assert (! (= orr_not__13 output_reg__14__arg__57) :named dyn25))
(assert (! (= output_reg__14 output_reg__14__result__55) :named dyn26))
(assert (! (> width__11 0) :named dyn27))
(assert (! (= width__49 8) :named dyn28))
(assert (! (> width__57 0) :named dyn29))
(assert (! (> width__40 0) :named dyn30))
(assert (! (> width__10 0) :named dyn31))
(assert (! (> width__47 0) :named dyn32))
(assert (! (> width__9 0) :named dyn33))
(assert (! (> width__50 0) :named dyn34))
(assert (! (> width__55 0) :named dyn35))
(assert (! (> width__44 0) :named dyn36))
(assert (! (> width__12 0) :named dyn37))
(assert (! (= width__19 8) :named dyn38))
(assert (! (= width__6 8) :named dyn39))
(assert (! (> width__13 0) :named dyn40))
(assert (! (= width__5 8) :named dyn41))
(assert (! (> width__14 0) :named dyn42))
(assert (! (> width__53 0) :named dyn43))
(assert (! (> width__42 0) :named dyn44))
(assert (! (> width__45 0) :named dyn45))
(assert (! (= width__35 8) :named dyn46))
(assert (! (= width__8 8) :named dyn47))
(assert (! (> width__54 0) :named dyn48))
(assert (! (= width__39 8) :named dyn49))
(assert (! (= width__40 width__40) :named dyn50))
(assert (! (= width__40 width__40) :named dyn51))
(assert (! (= width__9 width__40) :named dyn52))
(assert (! (= width__9 width__40) :named dyn53))
(assert (! (= width__42 width__42) :named dyn54))
(assert (! (= width__42 width__42) :named dyn55))
(assert (! (= width__9 width__44) :named dyn56))
(assert (! (= width__9 width__44) :named dyn57))
(assert (! (= width__10 width__42) :named dyn58))
(assert (! (= width__10 width__42) :named dyn59))
(assert (! (= width__11 width__45) :named dyn60))
(assert (! (= width__11 width__45) :named dyn61))
(assert (! (= width__12 width__47) :named dyn62))
(assert (! (= width__12 width__47) :named dyn63))
(assert (! (= width__11 width__53) :named dyn64))
(assert (! (= width__11 width__53) :named dyn65))
(assert (! (= width__12 width__54) :named dyn66))
(assert (! (= width__12 width__54) :named dyn67))
(assert (! (= width__13 width__50) :named dyn68))
(assert (! (= width__13 width__50) :named dyn69))
(assert (! (= width__13 width__57) :named dyn70))
(assert (! (= width__13 width__57) :named dyn71))
(assert (! (= width__14 width__55) :named dyn72))
(assert (! (= width__14 width__55) :named dyn73))
(assert (! (= bnot__8_narrow__8 bnot__8) :named dyn74))
(assert (! (= bnot__8_wide__8 (concat fresh0 bnot__8_narrow__8)) :named dyn75))
(assert (! (= bnot__8__result__35_narrow__35 bnot__8__result__35) :named dyn76))
(assert (! (= bnot__8__result__35_wide__35 (concat fresh1 bnot__8__result__35_narrow__35)) :named dyn77))
(assert (! (= bnot__8__x__19_narrow__19 bnot__8__x__19) :named dyn78))
(assert (! (= bnot__8__x__19_wide__19 (concat fresh2 bnot__8__x__19_narrow__19)) :named dyn79))
(assert (! (= has_type__9 has_type__9) :named dyn80))
(assert (! (= has_type__9__arg__39_narrow__39 has_type__9__arg__39) :named dyn81))
(assert (! (= has_type__9__arg__39_wide__39 (concat fresh3 has_type__9__arg__39_narrow__39)) :named dyn82))
(assert (! (= has_type__9__result__40 has_type__9__result__40) :named dyn83))
(assert (! (= lower__10 lower__10) :named dyn84))
(assert (! (= lower__10__arg__44 lower__10__arg__44) :named dyn85))
(assert (! (= lower__10__result__42 lower__10__result__42) :named dyn86))
(assert (! (= orr_not__13 orr_not__13) :named dyn87))
(assert (! (= orr_not__13__a__53 orr_not__13__a__53) :named dyn88))
(assert (! (= orr_not__13__b__54 orr_not__13__b__54) :named dyn89))
(assert (! (= orr_not__13__result__50 orr_not__13__result__50) :named dyn90))
(assert (! (= output_reg__14 output_reg__14) :named dyn91))
(assert (! (= output_reg__14__arg__57 output_reg__14__arg__57) :named dyn92))
(assert (! (= output_reg__14__result__55 output_reg__14__result__55) :named dyn93))
(assert (! (= put_in_reg__12 put_in_reg__12) :named dyn94))
(assert (! (= put_in_reg__12__arg__49_narrow__49 put_in_reg__12__arg__49) :named dyn95))
(assert (! (= put_in_reg__12__arg__49_wide__49 (concat fresh4 put_in_reg__12__arg__49_narrow__49)) :named dyn96))
(assert (! (= put_in_reg__12__result__47 put_in_reg__12__result__47) :named dyn97))
(assert (! (= x__clif1__5_narrow__5 x__clif1__5) :named dyn98))
(assert (! (= x__clif1__5_wide__5 (concat fresh5 x__clif1__5_narrow__5)) :named dyn99))
(assert (! (= zero_reg__11 zero_reg__11) :named dyn100))
(assert (! (= zero_reg__11__result__45 zero_reg__11__result__45) :named dyn101))
(check-sat)
(get-value (width__11))
(get-value (width__49))
(get-value (width__57))
(get-value (width__40))
(get-value (width__10))
(get-value (width__47))
(get-value (width__9))
(get-value (width__50))
(get-value (width__55))
(get-value (width__44))
(get-value (width__12))
(get-value (width__19))
(get-value (width__6))
(get-value (width__13))
(get-value (width__5))
(get-value (width__14))
(get-value (width__53))
(get-value (width__42))
(get-value (width__45))
(get-value (width__35))
(get-value (width__8))
(get-value (width__54))
(get-value (width__39))
