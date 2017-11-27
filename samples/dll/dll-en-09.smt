(set-logic QF_SLRDI)

(declare-sort Ldll_t 0)

(declare-fun next() (Field Ldll_t Ldll_t))
(declare-fun prev() (Field Ldll_t Ldll_t))

(define-fun dllseg
	((?E Ldll_t) (?P Ldll_t) (?F Ldll_t) (?L Ldll_t) ) Space
	(tospace
		 (or
			(and
				(= ?E ?F)
				(= ?P ?L)
			)
			(exists
				((?X Ldll_t))
				(and
					(tobool
						(ssep
							(pto ?E (sref (ref next ?X) (ref prev ?P) ))
							(dllseg ?X ?E  ?F ?L)
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




;; phi
(assert (and
    (tobool
        (ssep
            (dllseg E1 E1_p E2 E2_p)
            (dllseg E2 E2_p E3 E3_p)
        ))
        )
)

;; psi
(assert

(not    (tobool
        (dllseg E1 E1_p  E3 E3_p)
    ))
)

(check-sat)
