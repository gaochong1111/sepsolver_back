
(set-logic QF_SLRDI)

(declare-sort Ldll_t 0)

(declare-sort Sll_t 0)


;; declare fields
(declare-fun next1 () (Field Sll_t Sll_t))
(declare-fun data1 () (Field Sll_t Int))

(declare-fun next() (Field Ldll_t Ldll_t))
(declare-fun prev() (Field Ldll_t Ldll_t))
(declare-fun data() (Field Ldll_t Int))


;; declare predicates

(define-fun lsls 
	((?in Sll_t) (?dt1 Int) (?len1 Int) (?out Sll_t) (?dt2 Int) (?len2 Int)) 
	Space 
	(tospace 
		(or 
			(and (= ?in ?out) (= ?dt1 ?dt2) (= ?len1 ?len2) 
			(tobool emp)
			)

 
			(exists 
				((?u Sll_t
				) (?dt3 Int) (?len3 Int))
				(and  	
					(< ?dt1 (+ ?dt3 0))
					(= ?len1 (+ ?len3 1))
					(tobool (ssep 
						(pto ?in (sref (ref next1 ?u) (ref data1 ?dt1)) ) 
						(lsls ?u ?dt3 ?len3 ?out ?dt2 ?len2)
						) 
					)

				)
 

			)
		)
	)
)



(define-fun dll
	((?E Ldll_t) (?P Ldll_t) (?x1 Int) (?len1 Int) (?F Ldll_t) (?L Ldll_t) (?x2 Int) (?len2 Int)) Space
	(tospace
		 (or
			(and
				(= ?E ?F)
				(= ?P ?L)
				(= ?x1 ?x2)
				(= ?len1 ?len2)
				(tobool emp)
			)
			(exists
				((?X Ldll_t) (?x3 Int) (?len3 Int))
				(and					
					(< ?x1 (+ ?x3 0))
					(= ?len1 (+ ?len3 1))
					(tobool
						(ssep
							(pto ?E (sref (ref next ?X) (ref prev ?P) (ref data ?x1)))
							(dll ?X ?E ?x3 ?len3 ?F ?L ?x2 ?len2)
						)
					)
				)
			)
		)
	)
)

;; declare variables
(declare-fun y_emp () Sll_t)
(declare-fun w_emp () Sll_t)
(declare-fun z_emp () Sll_t)
(declare-fun d1 () Int)
(declare-fun d2 () Int)
(declare-fun n1 () Int)
(declare-fun n2 () Int)



(declare-fun E1() Ldll_t)
(declare-fun E2() Ldll_t)
(declare-fun E3() Ldll_t)
(declare-fun E4() Ldll_t)
(declare-fun x1() Int)
(declare-fun x2() Int)
(declare-fun len1() Int)
(declare-fun len2() Int)
(declare-fun x() Int)



(assert 
	(and
	(distinct d1 d2)
	(= n1 (+ n2 3))
	(= len1 (+ len2 3))
	(>= len2 0)
	(>= n2 0)
	(tobool 
 	        (ssep 
		        (pto z_emp (sref (ref next1 y_emp) (ref data1 d1)) )
			    (lsls y_emp d1 n1 w_emp d2 n2)
				(pto E3 (sref (ref next E4) (ref prev E2) (ref data x)))
				(dll E1 E3 x1 len1 E2 E4 x2 len2)
		)
	)
	)
)

(check-sat)
(get-model)
;; unsat




