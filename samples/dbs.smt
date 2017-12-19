

(declare-sort Sls_t 0)
(declare-fun next() (Field Sls_t Sls_t))

(define-fun sls ((?E Sls_t) (?S SetInt) (?F Sls_t) (?S1 SetInt)) Space
    (tospace
        (or
            (and (= ?E ?F) (= ?S ?S1))

            (exists ((?X Sls_t) (?S2 SetInt))
                    (and (= ?S (setunion ?S2 (set (min ?S))))
                         (= (min ?S2) (+ (min ?S) 1))
                         (tobool (ssep
                                 (pto ?E (ref next ?X))
                                 (sls ?X ?S2 ?F ?S1)
                         ))
                    )
            )
        )
    )
)


(declare-fun S1() SetInt)
(declare-fun S2() SetInt)

(assert ( <=
          (max (setunion S1 S2))
          (+ (min S1) 2)
        )
)