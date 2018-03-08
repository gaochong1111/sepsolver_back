
(set-logic QF_SLRDI)

(declare-sort Sls_t 0)
(declare-fun next() (Field Sls_t Sls_t))
(declare-fun data() (Field Sls_t Int))


(define-fun sls ((?E Sls_t) (?S SetInt) (?F Sls_t) (?S1 SetInt)) Space
    (tospace
        (or
            (and (= ?E ?F) (= ?S ?S1))

            (exists ((?X Sls_t) (?S2 SetInt))
                    (and
                        (= ?S (setunion ?S2 (setunion (set (min ?S)) (set (max ?S)))))
                        (= (min ?S2) (+ (min ?S) 2))
                        (= (max ?S) (+ (max ?S2) 3))
                        (tobool (ssep
                                 (pto ?E (sref (ref next ?X) (ref data min(?S))))
                                 (sls ?X ?S2 ?F ?S1)
                         ))
                    )
            )
        )
    )
)


(declare-fun S1() SetInt)
(declare-fun S2() SetInt)
(declare-fun S3() SetInt)
(declare-fun S4() SetInt)
(declare-fun S() SetInt)


(declare-fun E() Sls_t)
(declare-fun F() Sls_t)
(declare-fun E1() Sls_t)
(declare-fun F1() Sls_t)

(declare-fun x1() Int)
(declare-fun x2() Int)
(declare-fun x3() Int)


(assert (and
        ;(= S2 (setminus S S3))
        ; (= (min S2)  (+ (min S1) 8))
        (not (and
            (distinct (min S2)  (+ (min S1) 6))
            (distinct (min S2)  (+ (min S1) 8))
            )
        )
        

        ; (= (min S1) (+ (max S3) 1))
        ; (= (min S4)  (+ (min S3) 8))
        (distinct S1 S2)
        ;(> (min S1) 2)
        ; (>= (- (+ x2 x3) x1) 0)
        (= (- (* 5 (- (min S2) (min S1))) (* 3 (- (max S1) (max S2)))) 0)
        ;


        (tobool
            ; (ssep (sls E S1 F S2) (sls E1  S3 F1  S4))
            (sls E S1 F S2)
        )
)

)

(check-sat)
