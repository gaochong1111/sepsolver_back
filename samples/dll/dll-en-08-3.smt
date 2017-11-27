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

(declare-fun E1_p() Ldll_t)
(declare-fun E2_p() Ldll_t)


(declare-fun x1() Int)
(declare-fun x2() Int)


;; phi
(assert (and
        (= x1 (+ x2 1))
        (= E1 E2_p)
        (tobool
            (pto E1 (sref (ref next E2) (ref prev E1_p)))
        ))
)

;; psi
(assert
(not (and true
     (tobool
        (ldllseg E1 E1_p x1 E2 E2_p x2)
)))

)
(check-sat)
