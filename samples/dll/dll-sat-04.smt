(set-logic QF_SLRDI)

(declare-sort Ldll_t 0)

(declare-fun next() (Field Ldll_t Ldll_t))
(declare-fun prev() (Field Ldll_t Ldll_t))

(define-fun dll
	((?E Ldll_t) (?P Ldll_t) (?x0 Int) (?F Ldll_t) (?L Ldll_t) (?x1 Int) (sta_n Int)) Space
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
					;; (<= ?x0 (+ sta_n -2))
					;; (<= ?x0 (+ ?x2 -1))
					(>= ?x0 (+ sta_n 0))
					(= ?x0 (+ ?x2 1))
					(tobool
						(ssep
							(pto ?E (sref (ref next ?X) (ref prev ?P) ))
							(dll ?X ?E ?x2 ?F ?L ?x1 sta_n)
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
(declare-fun n1() Int)
(declare-fun n2() Int)

(declare-fun n3() Int)


(assert
	(and
		(< n2 0)
		(>= n3 2)
		(= n1 (+ n2 2))
		(tobool
			(ssep
				(pto E3 (sref (ref next E4) (ref prev E2)))
			 	(dll E1 E3 n1 E2 E4 n2 n3)
			)
		)
	)
)

(check-sat)

;; unsat

