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

(define-fun sls ((?E Lst_t) (?d1 Int)  (?F Lst_t) (?d2 Int)) Space (tospace 
    (or 
    (and (= ?E ?F) 
        (= ?d1 ?d2)
        (tobool emp
        )
    )
 
    (exists ((?X Lst_t)  (?d3 Int)) 
    (and  (<= ?d1 (+ ?d3 0) )
        (tobool (ssep 
        (pto ?E (sref (ref next ?X) (ref data ?d1)) ) 
        (sls ?X ?d3 ?F ?d2)
        )
        )
        
    ) 
    )
    )
))

;; declare variables
(declare-fun root () Lst_t)
(declare-fun cur () Lst_t)
(declare-fun cur2 () Lst_t)
(declare-fun X () Lst_t)
(declare-fun Y () Lst_t)
(declare-fun key () Int)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun z1 () Int)
(declare-fun z2 () Int)


(assert 
    (and
    (< z key)
    (<=  z z1)
    (distinct cur nil)
    (< z1 key)
    (<= z1 z2)
    (= cur2 Y)
    (tobool 
    (ssep 
        (sls root x X z)  
        (pto X (sref (ref next cur) (ref data z) ) )
        (pto cur (sref (ref next Y) (ref data z1) ) ) 
        (sls Y z2 nil y) 
    ))
    )
)

(assert (not 
    (and 
    (< z1 key)
    (<= z1 z2)
    (tobool 
    (ssep 
        (sls root x cur z1)  
        (pto cur (sref (ref next cur2) (ref data z1) ) ) 
        (sls cur2 z2 nil y) 
    ))
    )
    )
)

(check-sat)