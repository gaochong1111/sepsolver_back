(set-logic QF_SLRDI)

(declare-sort sls_t 0)
;(declare-sort Lseg_t 0)


(declare-fun next () (Field sls_t sls_t))
(declare-fun data () (Field sls_t Int))

(
define-fun slseg ((?E sls_t) (?d1 Int)  (?F sls_t) (?d2 Int) ) Space
	(tospace 
		(or
			(and (= ?E ?F) (= ?d1 ?d2)
			(tobool emp)
			)

			(exists ((?X sls_t) (?d5 Int) )
				(and
					(= ?d1 (+ ?d5 1))
					(tobool (ssep
							(pto ?E (sref (ref next ?X) (ref data ?d5)))
							(slseg ?X ?d5  ?F ?d2 )
					    	)
					)
				)
			)
		)
	)
)



(declare-fun X () sls_t)
(declare-fun Y () sls_t)
(declare-fun Z () sls_t)

(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)


(assert
	(and
		;(< a b)
		(tobool
			(ssep
				(slseg X a Y b )
                (slseg Y b Z c)
			)
		)
	)
)

(assert
	(not
	(and
		(tobool
			(slseg X a Z c)
	)
	)
)
)

(check-sat)
