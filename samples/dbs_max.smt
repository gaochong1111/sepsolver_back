
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
                        (= ?S (setunion ?S2 (set (max ?S))))
                        (= (max ?S2) (- (max ?S) 1))
                        (tobool (ssep
                                 (pto ?E (sref (ref next ?X) (ref data max(?S))))
                                 (sls ?X ?S2 ?F ?S1)
                         ))
                    )
            )
        )
    )
)


(declare-fun S1() SetInt)
(declare-fun S2() SetInt)

(declare-fun E() Sls_t)
(declare-fun F() Sls_t)

(assert (and
        ; (distinct E F)
        ; (= (min S2) (+ min(S1) 5))
        (= (max S1) (+ (max S2) 5))
        ; (< (max S1) 6)

        (tobool
            (sls E S1 F S2)
        )
)

)

(check-sat)