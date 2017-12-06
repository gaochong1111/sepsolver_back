(set-logic QF_SLRDI)

;; declare sorts
(declare-sort Dll_t 0)


;; declare fields
(declare-fun next () (Field Dll_t Dll_t))
(declare-fun prev () (Field Dll_t Dll_t))


;; declare predicates

(define-fun dll ((?E Dll_t) (?P Dll_t) (?F Dll_t) (?L Dll_t)) Space (tospace 
	(or 
	(and (= ?E ?F) (= ?P ?L)
		(tobool emp
		)

	)
 
	(exists ((?u Dll_t)) 
	(and 
		(tobool (ssep 
		(pto ?E (sref (ref next ?u) (ref prev ?P) ) ) 
		(dll ?u ?E ?F ?L)
		) )

	)
 
	)

	)
))
;; declare variables
(declare-fun x_emp () Dll_t)
(declare-fun w_emp () Dll_t)
(declare-fun y_emp () Dll_t)
(declare-fun z_emp () Dll_t)
(declare-fun u_emp () Dll_t)



(assert 
	(and (distinct x_emp w_emp) (distinct x_emp z_emp) (distinct y_emp z_emp) 
	(tobool 
	(ssep 
		(pto x_emp (sref (ref next w_emp) (ref prev nil) ) ) 
	    (dll w_emp x_emp y_emp u_emp )
		(pto y_emp (sref (ref next z_emp) (ref prev u_emp) ) ) 
	)

	)

	)

)

(assert (not 
	(tobool 
	 (dll x_emp nil z_emp y_emp )
	)

))

(check-sat)
