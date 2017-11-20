(set-logic QF_SLRDI)

(declare-sort Ldll_t 0)

(declare-fun next() (Field Ldll_t Ldll_t))
(declare-fun prev() (Field Ldll_t Ldll_t))

(define-fun ldllseg
	((?E Ldll_t) (?P Ldll_t) (?x0 Int) (?F Ldll_t) (?L Ldll_t) (?x1 Int)) Space
	(tospace
		 (or
			(and
				(= ?E ?F)
				(= ?P ?L)
				(= ?x0 ?x1) 
			)
			(exists
				((?X Ldll_t) (?x2 Int))
				(and
					;(<= ?x0 0)
					(>= ?x0 2)
					(= ?x0 (+ ?x2 1))
					(tobool
						(ssep
							(pto ?E (sref (ref next ?X) (ref prev ?P) ))
							(ldllseg ?X ?E ?x2 ?F ?L ?x1)
						)
					)
				)
			)
		)
	)
)


(declare-fun E1() Ldll_t)
(declare-fun E2() Ldll_t)
(declare-fun E3() Ldll_t)
(declare-fun E4() Ldll_t)
(declare-fun E5() Ldll_t)
(declare-fun E6() Ldll_t)

(declare-fun E7() Ldll_t)
(declare-fun E8() Ldll_t)
(declare-fun E9() Ldll_t)


(declare-fun E1_prime() Ldll_t)
(declare-fun E2_prime() Ldll_t)
(declare-fun E3_prime() Ldll_t)
(declare-fun E4_prime() Ldll_t)
(declare-fun E5_prime() Ldll_t)
(declare-fun E6_prime() Ldll_t)

(declare-fun x1() Int)
(declare-fun x2() Int)
(declare-fun x3() Int)
(declare-fun x4() Int)
(declare-fun x5() Int)
(declare-fun x6() Int)
(declare-fun x3_prime() Int)
(declare-fun x4_prime() Int)
(declare-fun x5_prime() Int)



;; phi
(assert (and
    (tobool
        (ssep
            (ldllseg E1 E1_prime x1 E3 E3_prime x3)
            (ldllseg E2 E2_prime x2 E4 E4_prime x4)
            (ldllseg E3 E3_prime x3 E4 E7 x4)
            (ldllseg E4 E4_prime x4_prime E3 E8 x3_prime)
            (ldllseg E3 E3_prime x3 E5 E5_prime x5)
            (ldllseg E5 E5_prime x5_prime E3 E9 x3_prime)
            (ldllseg E4 E4_prime x4 E6 E6_prime x6)
        ))
        )
)

;; psi
(assert (not (tobool
        (ldllseg E1 E1_prime x1 E3 E3_prime x3)
)
))

(check-sat)
