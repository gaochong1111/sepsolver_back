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
				(tobool emp)
			)
			(exists
				((?X Ldll_t) (?x2 Int))
				(and
					;(>= ?x0 5)
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
(define-fun dllseg1
	((?E Ldll_t) (?F Ldll_t)) Space
	(tospace
		 (or
			(and
				(= ?E ?F) (tobool emp)
			)
			(exists
				((?X Ldll_t) (?Y Ldll_t))
				(and
					;(>= ?x0 5)
					;(= ?x0 (+ ?x2 1))
					(tobool
						(ssep
							(pto ?E (sref (ref next ?X) (ref prev ?Y) ))
							(dllseg1 ?X ?F)
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

(declare-fun x1() Int)
(declare-fun x2() Int)
(declare-fun x3() Int)
(declare-fun x4() Int)
(declare-fun x5() Int)
(declare-fun x6() Int)

(declare-fun y3() Int)
(declare-fun y4() Int)
(declare-fun y5() Int)

(declare-fun alpha0() SetLoc)
(declare-fun alpha1() SetLoc)

(assert
	(and
		;(> x3 x5)
		;(> y4 y3)
		;(= E3 E5)
		;(= E4 E3)
		;(>= n1 (+ n2 5))
		(tobool
		(ssep   (index alpha0 (ldllseg E1 F1 x1 E3 F3 x3)) 
			(index alpha0 (ldllseg E2 F2 x2 E4 F4 x4))
			(index alpha0 (ldllseg E3 F3 x3 E4 F4 x4))
			(index alpha0 (ldllseg E4 F4 y4 E3 F3 y3))
			(index alpha0 (ldllseg E3 F3 x3 E5 F5 x5))
			(index alpha0 (ldllseg E5 F5 y5 E3 F3 y3))
			(index alpha0 (ldllseg E4 F4 x5 E6 F6 x6))
		) 
		)
	)
)

(assert
	(not
		(and
			;(distinct E1 E3)
			(tobool
				(ssep (index alpha0 (dllseg1 E1 E3))
					(index alpha1 (dllseg1 E2 E6))
				)
			)
		)
	)
)

(check-sat)
