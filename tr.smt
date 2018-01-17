(let ((a!1 (= ?S (setunion ?S1 (set (max ?S)))))
      (a!2 (and true (>= (max ?S) (+ (min ?S) 1))))
      (a!3 (and true (<= (min ?S1) (+ (max ?S1) 0))))
      (a!5 (not (not (forall ((E_S1 SetInt) (E_S2 SetInt))
                       (let ((a!1 (= ?S (setunion E_S1 (set (max ?S)))))
                             (a!2 (= E_S2 (setunion ?S1 (set (max E_S2)))))
                             (a!3 (not (not (forall ((ES_X SetInt))
                                              (let ((a!1 (and (>= (min ES_X)
                                                                  (+ (max E_S2)
                                                                     1))
                                                              (= ES_X
                                                                 (setminus E_S1
                                                                           E_S2)))))
                                                (not a!1))))))
                             (a!5 (and true (>= (max ?S) (+ (min ?S) 1))))
                             (a!6 (and true (<= (min ?S1) (+ (max ?S1) 0))))
                             (a!7 (forall ((x Int) (y Int))
                                    (let ((a!1 (subset (set x)
                                                       (setunion (setminus E_S1
                                                                           E_S2)
                                                                 (set (max E_S2)))))
                                          (a!2 (subset (set y)
                                                       (setunion (setminus E_S1
                                                                           E_S2)
                                                                 (set (max E_S2)))))
                                          (a!3 (forall ((z Int))
                                                 (let ((a!1 (subset (set z)
                                                                    (setunion (setminus E_S1
                                                                                        E_S2)
                                                                              (set (max E_S2))))))
                                                   (not (and a!1
                                                             (>= z (+ x 1))
                                                             (>= y (+ z 1)))))))
                                          (a!4 (not (and true
                                                         (<= y (+ x 1))
                                                         (>= y (+ x 1))))))
                                      (not (and a!1 a!2 (>= y (+ x 1)) a!3 a!4))))))
                       (let ((a!4 (and (not (= (setminus E_S1 E_S2) emptyset))
                                       a!3)))
                       (let ((a!8 (and a!1
                                       a!2
                                       (subset E_S2 E_S1)
                                       (not (= ?S1 emptyset))
                                       (not a!4)
                                       true
                                       (<= (max ?S) (+ (max E_S1) 1))
                                       (>= (max ?S) (+ (max E_S1) 1))
                                       true
                                       (<= (max E_S2) (+ (max ?S1) 1))
                                       (>= (max E_S2) (+ (max ?S1) 1))
                                       a!5
                                       true
                                       (>= (max E_S2) (+ (min E_S2) 1))
                                       a!6
                                       true
                                       (<= (min E_S1) (+ (max E_S1) 0))
                                       a!7)))
                         (not a!8)))))))))
(let ((a!4 (and a!1
                true
                (<= (min ?S) (+ (min ?S1) 0))
                (<= (min ?S1) (+ (min ?S) 0))
                a!2
                true
                (<= (min ?S) (+ (max ?S1) 0))
                true
                (>= (max ?S) (+ (min ?S1) 1))
                a!3
                true
                (<= (max ?S) (+ (max ?S1) 1))
                (>= (max ?S) (+ (max ?S1) 1)))))
  (not (and (not (= ?S ?S1)) (not a!4) a!5))))
