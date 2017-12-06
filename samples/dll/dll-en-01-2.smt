(set-logic QF_SLRDI)

(declare-sort Ldll_t 0)

(declare-fun next() (Field Ldll_t Ldll_t))
(declare-fun prev() (Field Ldll_t Ldll_t))
(declare-fun data() (Field Ldll_t Int))


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
(declare-fun E4() Ldll_t)
(declare-fun E5() Ldll_t)
(declare-fun E6() Ldll_t)

(declare-fun F1() Ldll_t)
(declare-fun F2() Ldll_t)
(declare-fun F3() Ldll_t)
(declare-fun F4() Ldll_t)
(declare-fun F5() Ldll_t)
(declare-fun F6() Ldll_t)




(assert
	(and
		;(= E3 E5)
		;(= E4 E3)
		(tobool
		(ssep   (dllseg E1 F1 E3 F3)
				 (dllseg E2 F2 E4 F4)
			 (dllseg E3 F3  E4 F4)
			 (dllseg E4 F4  E3 F3)
			 (dllseg E3 F3  E5 F5)
			 (dllseg E5 F5  E3 F3)
			 (dllseg E4 F4  E6 F6)
		) 
		)
	)
)


(assert
	(not
		(and
			;(= E1 E2)
			(tobool
				(ssep  (dllseg E1 F1 E3 F3)
					   (dllseg E2 F2 E6 F6)
				)
			)
		)
	)
)


(check-sat)
