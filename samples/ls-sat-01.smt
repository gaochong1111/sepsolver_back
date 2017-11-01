
(set-logic QF_S)

;; declare sorts
(declare-sort Sll_t 0)


;; declare fields
(declare-fun next () (Field Sll_t Sll_t))
(declare-fun data () (Field Sll_t Int))


;; declare predicates

(define-fun ls ((?E Sll_t) (?x Int) (?l Int) (?F Sll_t) (?x1 Int) (?l1 Int)) Space (tospace 
	(or 
	(and (= ?E ?F)
		 (= ?x ?x1)
		 (= ?l ?l1)
		(tobool emp
		)

	)
 
	(exists ((?X Sll_t) (?x2 Int) (?l2 Int)) 
	(and
		(= ?l (+ ?l2 -1))
		(<= ?l (+ ?l2 -1))
		(>= ?l (+ ?l2 2))
		(> ?l -2)
		(> ?l 2)
		(< ?l 3)
		(> ?x (+ ?x2 -1))
		(tobool (ssep 
				(pto ?E (sref (ref next ?X) (ref data ?x)) ) 
				(ls ?X ?x2 ?l2 ?F ?x1 ?l1)
		))
	)
 
	)

	)
))

;; declare variables
(declare-fun y_emp () Sll_t)
(declare-fun w_emp () Sll_t)
(declare-fun z_emp () Sll_t)
(declare-fun x_emp () Int)
(declare-fun x1_emp () Int)
(declare-fun l_emp () Int)
(declare-fun l1_emp () Int)




(assert 
	(tobool 
 	        (ssep 
                (pto y_emp (ref next z_emp))
				(ls y_emp x_emp l_emp w_emp x1_emp l1_emp)
				(pto w_emp (ref next z_emp )) 
		)
	)
)

(check-sat)
