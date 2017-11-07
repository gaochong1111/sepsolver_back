
(set-logic QF_S)

;; declare sorts
(declare-sort Sll_t 0)


;; declare fields
(declare-fun next () (Field Sll_t Sll_t))


;; declare predicates

(define-fun ls ((?in Sll_t) (?out Sll_t) ) Space (tospace 
	(or 
	(and (= ?in ?out) 
		(tobool emp
		)

	)
 
	(exists ((?u Sll_t) ) 
	(and
		(tobool (ssep 
		(pto ?in (ref next ?u) ) 
		(ls ?u ?out )
		) )
	) 
	)
	)
))

;; declare variables
(declare-fun y_emp () Sll_t)
(declare-fun w_emp () Sll_t)
(declare-fun z_emp () Sll_t)

;; declare set of locations

(assert 
	(tobool 
 	        (ssep 
                (pto y_emp (ref next z_emp))
				(ls y_emp w_emp )
				(pto w_emp (ref next z_emp )) 
		)
	)
)

(check-sat)

;; unsat
