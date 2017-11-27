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
					; (>= ?x0 2)
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

(declare-fun E1_p() Ldll_t)
(declare-fun E2_p() Ldll_t)
(declare-fun E3_p() Ldll_t)


(declare-fun x1() Int)
(declare-fun x2() Int)
(declare-fun x3() Int)
(declare-fun x4() Int)





;; phi
(assert (and
        ;(= x1 (+ x2 1))
        (tobool
            (ssep
                (ldllseg E1 E1_p x1 E2 E2_p x2)
                (pto E2 (sref (ref next E3) (ref prev E2_p)))
                (ldllseg E2 E2_p x2 E3 E3_p x3)
        )))
)

;; psi
(assert
(not (and true
     (tobool
        (ldllseg E1 E1_p x1 E3 E3_p x3)
)))

)
(check-sat)
