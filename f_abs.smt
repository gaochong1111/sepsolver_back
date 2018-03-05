(let ((a!1 (setunion S2 (setunion (set (min S1)) (set (max S1)))))
      (a!3 (setunion S1_1 (setunion (set (min S1)) (set (max S1)))))
      (a!4 (setunion S1_2 (setunion (set (min S1_1)) (set (max S1_1)))))
      (a!5 (setunion S2 (setunion (set (min S1_2)) (set (max S1_2)))))
      (a!6 (and true (>= (max S1_2) (+ (min S1_2) 5))))
      (a!7 (and true (<= (min S2) (+ (max S2) 0)))))
(let ((a!2 (and (and |[E,0]| (>= E 1))
                (= S1 a!1)
                (= (min S2) (+ (min S1) 2))
                (= (max S1) (+ (max S2) 3))))
      (a!8 (and (= S1_2 a!5)
                true
                (= (min S2) (+ (min S1_2) 2))
                a!6
                true
                (>= (max S2) (+ (min S1_2) 2))
                true
                (>= (max S1_2) (+ (min S2) 3))
                a!7
                true
                (= (max S1_2) (+ (max S2) 3)))))
(let ((a!9 (not (and (not (= S1_2 S2))
                     (not a!8)
                     (forall ((E_S1 SetInt)
                              (E_S2 SetInt)
                              (E_S3 SetInt)
                              (E_S4 SetInt))
                       (let ((a!1 (setunion E_S1
                                            (setunion (set (min S1_2))
                                                      (set (max S1_2)))))
                             (a!2 (setunion S2
                                            (setunion (set (min E_S2))
                                                      (set (max E_S2)))))
                             (a!3 (not (and (not (= E_S3 emptyset))
                                            (>= (max E_S3) (min E_S2)))))
                             (a!4 (not (and (not (= E_S4 emptyset))
                                            (>= (max E_S2) (min E_S4)))))
                             (a!5 (and true (>= (max S1_2) (+ (min S1_2) 5))))
                             (a!6 (and true (<= (min S2) (+ (max S2) 0))))
                             (a!7 (= (* 3 (- (min S2) (min S1_2)))
                                     (* 2 (- (max S1_2) (max S2))))))
                       (let ((a!8 (and (= S1_2 a!1)
                                       (= E_S1
                                          (setunion (setunion E_S2 E_S3) E_S4))
                                       (= E_S2 a!2)
                                       a!3
                                       a!4
                                       true
                                       (= (min S2) (+ (min E_S2) 2))
                                       true
                                       (= (min E_S1) (+ (min S1_2) 2))
                                       a!5
                                       true
                                       (>= (max E_S2) (+ (min E_S2) 5))
                                       true
                                       (>= (max S2) (+ (min E_S2) 2))
                                       true
                                       (>= (max E_S1) (+ (min S1_2) 2))
                                       true
                                       (>= (max E_S2) (+ (min S2) 3))
                                       true
                                       (>= (max S1_2) (+ (min E_S1) 3))
                                       a!6
                                       true
                                       (<= (min E_S1) (+ (max E_S1) 0))
                                       true
                                       (= (max E_S2) (+ (max S2) 3))
                                       true
                                       (= (max S1_2) (+ (max E_S1) 3))
                                       (forall ((x Int) (y Int))
                                         (let ((a!1 (subset (set x)
                                                            (setunion E_S3
                                                                      (set (min E_S2)))))
                                               (a!2 (subset (set y)
                                                            (setunion E_S3
                                                                      (set (min E_S2)))))
                                               (a!3 (not (and true
                                                              (= y (+ x 2))))))
                                         (let ((a!4 (and a!1
                                                         a!2
                                                         (>= y (+ x 1))
                                                         (forall ((z Int))
                                                           (let ((a!1 (subset (set z)
                                                                              (setunion E_S3
                                                                                        (set (min E_S2)))))
                                                                 (a!2 (and (>= z
                                                                               (+ x
                                                                                  1))
                                                                           (>= y
                                                                               (+ z
                                                                                  1)))))
                                                             (not (and a!1 a!2))))
                                                         a!3)))
                                           (not a!4))))
                                       (forall ((x Int) (y Int))
                                         (let ((a!1 (subset (set x)
                                                            (setunion E_S4
                                                                      (set (max E_S2)))))
                                               (a!2 (subset (set y)
                                                            (setunion E_S4
                                                                      (set (max E_S2)))))
                                               (a!3 (not (and true
                                                              (= y (+ x 3))))))
                                         (let ((a!4 (and a!1
                                                         a!2
                                                         (>= y (+ x 1))
                                                         (forall ((z Int))
                                                           (let ((a!1 (subset (set z)
                                                                              (setunion E_S4
                                                                                        (set (max E_S2)))))
                                                                 (a!2 (and (>= z
                                                                               (+ x
                                                                                  1))
                                                                           (>= y
                                                                               (+ z
                                                                                  1)))))
                                                             (not (and a!1 a!2))))
                                                         a!3)))
                                           (not a!4))))
                                       a!7)))
                         (not a!8))))))))
(let ((a!10 (and (and |[E,0]| (>= E 1))
                 (= S1 a!3)
                 (= (min S1_1) (+ (min S1) 2))
                 (= (max S1) (+ (max S1_1) 3))
                 (= S1_1 a!4)
                 (= (min S1_2) (+ (min S1_1) 2))
                 (= (max S1_1) (+ (max S1_2) 3))
                 a!9)))
(let ((a!11 (and (not (and (not |[E,0]|) (= E F) (= S1 S2)))
                 (not a!2)
                 (not a!10))))
  (and (= (min S2) (+ (min S1) 6)) (distinct S1 S2) (not a!11) true))))))
