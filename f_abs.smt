(let ((a!1 (= S1 (setunion S2 (set (max S1)))))
      (a!3 (= S1 (setunion S1_1 (set (max S1)))))
      (a!4 (= S1_1 (setunion S1_2 (set (max S1_1)))))
      (a!5 (= S1_2 (setunion S2 (set (max S1_2)))))
      (a!6 (and true (>= (max S1_2) (+ (min S1_2) 1))))
      (a!7 (and true (<= (min S2) (+ (max S2) 0))))
      (a!9 (not (not (forall ((E_S1 SetInt) (E_S2 SetInt))
                       (let ((a!1 (= S1_2 (setunion E_S1 (set (max S1_2)))))
                             (a!2 (= E_S2 (setunion S2 (set (max E_S2)))))
                             (a!3 (not (not (forall ((ES_X SetInt))
                                              (let ((a!1 (and (>= (min ES_X)
                                                                  (+ (max E_S2)
                                                                     1))
                                                              (= ES_X
                                                                 (setminus E_S1
                                                                           E_S2)))))
                                                (not a!1))))))
                             (a!5 (and true (>= (max S1_2) (+ (min S1_2) 1))))
                             (a!6 (and true (<= (min S2) (+ (max S2) 0))))
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
                                       (not (= S2 emptyset))
                                       (not a!4)
                                       true
                                       (<= (max S1_2) (+ (max E_S1) 1))
                                       (>= (max S1_2) (+ (max E_S1) 1))
                                       true
                                       (<= (max E_S2) (+ (max S2) 1))
                                       (>= (max E_S2) (+ (max S2) 1))
                                       a!5
                                       true
                                       (>= (max E_S2) (+ (min E_S2) 1))
                                       a!6
                                       true
                                       (<= (min E_S1) (+ (max E_S1) 0))
                                       a!7)))
                         (not a!8)))))))))
(let ((a!2 (and (and |[E,0]| (>= E 1)) a!1 (= (max S1) (+ (max S2) 1))))
      (a!8 (and a!5
                true
                (<= (min S1_2) (+ (min S2) 0))
                (<= (min S2) (+ (min S1_2) 0))
                a!6
                true
                (<= (min S1_2) (+ (max S2) 0))
                true
                (>= (max S1_2) (+ (min S2) 1))
                a!7
                true
                (<= (max S1_2) (+ (max S2) 1))
                (>= (max S1_2) (+ (max S2) 1)))))
(let ((a!10 (not (and (not (= S1_2 S2)) (not a!8) a!9))))
(let ((a!11 (and (and |[E,0]| (>= E 1))
                 a!3
                 (= (max S1) (+ (max S1_1) 1))
                 a!4
                 (= (max S1_1) (+ (max S1_2) 1))
                 a!10)))
(let ((a!12 (and (not (and (not |[E,0]|) (= E F) (= S1 S2)))
                 (not a!2)
                 (not a!11))))
  (and (= (max S1) (+ (max S2) 5)) (not a!12) true))))))
