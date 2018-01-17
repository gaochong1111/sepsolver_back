

(declare-sort Dlls_t 0)
(declare-fun next() (Field Dlls_t Dlls_t))
(declare-fun prev() (Field Dlls_t Dlls_t))


(define-fun ldllseg ((?E Dlls_t) (?P Dlls_t) (?S SetInt) (?F Dlls_t) (?L Dlls_t) (?S1 SetInt)) Space
    (tospace
        (or
            (and (= ?E ?F) (= ?P ?L) (= ?S ?S1))

            (exists ((?X Dlls_t)  (?S2 SetInt))
                    (and
                        (= ?S (setunion ?S2 (set (max ?S))))
                        (= (max ?S2) (- (max ?S) 1))
                        (tobool (ssep
                                 (pto ?E (sref (ref next ?X) (ref prev ?P)))
                                 (ldllseg ?X ?E ?S2 ?F ?L ?S1)
                         ))
                    )
            )
        )
    )
)


(declare-fun S1() SetInt)
(declare-fun S2() SetInt)

(declare-fun E() Dlls_t)
(declare-fun P() Dlls_t)
(declare-fun F() Dlls_t)
(declare-fun L() Dlls_t)

(assert (and
        ; (distinct E F)
        ; (= (min S2) (+ min(S1) 5))
        (= (max S1) (+ (max S2) 5))

        (tobool
            (ldllseg E P S1 F L S2)
        )
)

)

(check-sat)