(set-logic QF_SLRDI)

(declare-sort sls_t 0)

(declare-fun next () (Field sls_t sls_t))

(
define-fun slseg ((?E sls_t) (?d1 Int) (?F sls_t) (?d2 Int)) Space
	(tospace 
		(or
			(and (= ?E ?F) (= ?d1 ?d2)
			(tobool emp)
			)

			(exists ((?X sls_t) (?d3 Int))
				(and
					(= ?d1 (+ ?d3 0) )
					(tobool (ssep
							(pto ?E (ref next ?X))
							(slseg ?X ?d3 ?F ?d2)
					    	)
					)
				)
			)
		)
	)
)

(declare-fun x () sls_t)
(declare-fun y () sls_t)
(declare-fun z () sls_t)
(declare-fun a () Int)
(declare-fun b () Int)


(assert
	(and
		;; (< a b)
		(tobool
			(ssep
				(pto x (ref next z))
			 	(slseg x a y b)
			)
		)
	)
)

(check-sat)
(get-model)
;; sat

