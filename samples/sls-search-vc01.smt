; Extending QF_S:
; constant emptybag, 
; the function bag, 
; the multiset comparison operator <=, bag-le, bag-gt, bag-ge
; bagunion, intersection, difference of multisets
; an element is contained in a multiset

(set-logic QF_SLRDI)

;; declare sorts
(declare-sort Lst_t 0)

;; declare fields
(declare-fun next () (Field Lst_t Lst_t))
(declare-fun data () (Field Lst_t Int))

;; declare predicates

(define-fun slseg ((?E Lst_t) (?d1 Int)  (?F Lst_t) (?d2 Int)) Space (tospace 
	(or 
	(and (= ?E ?F)
		 (= ?d1 ?d2)
		(tobool emp
		)
	)
 
	(exists ((?X Lst_t)  (?d3 Int)) 
	(and  (<= ?d1 (+ ?d3 0))
		(tobool (ssep 
		(pto ?E (sref (ref next ?X) (ref data ?d1)) ) 
		(slseg ?X ?d3 ?F ?d2)
		)
		)
		
	) 
	)
	)
))

;; declare variables
(declare-fun root () Lst_t)
(declare-fun cur1 () Lst_t)
(declare-fun X () Lst_t)
(declare-fun key () Int)
(declare-fun d () Int)
(declare-fun d0 () Int)
(declare-fun d1 () Int)
(declare-fun d2 () Int)
(declare-fun d3 () Int)
(declare-fun ret () Int)

;; declare set of locations

a
;; VC1: slseg(root, cur1, M0, M1) * cur1 |->((next,X), (data, d)) * slist(X,M2) & M1 = {d} cup M2 & d <= M2 & (key in M0 <=> key in M1) & 
;; cur1 != nil & d = key & ret = 1 |- 
;; slist(root, M0) & ret = 1 & key in M0


(assert 
	(and
    (<= d1 d)
	(<=  d d2)
	(= d key)
	(= ret 1)
	(tobool 
	(ssep 
	 (slseg root d0 cur1 d1) 
		(pto cur1 (sref (ref next X) (ref data d) ) ) 
		 (slseg X d2 nil d3) 
	))

	)
)

(assert (not 
	(and
    	(= ret 1)
	(tobool 
	 (slseg root d0 nil d3)
	)
	)
	)
)

(check-sat)
