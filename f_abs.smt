(let ((a!1 (= S1 (setunion S2 (set (min S1)))))
      (a!3 (= S1 (setunion S1_1 (set (min S1)))))
      (a!4 (= S1_1 (setunion S1_2 (set (min S1_1)))))
      (a!5 (= S1_2 (setunion S2 (set (min S1_2)))))
      (a!6 (and true (>= (max S1_2) (+ (min S1_2) 1))))
      (a!7 (and true (<= (min S2) (+ (max S2) 0))))
      (a!9 (not (not (forall ((E_S1 SetInt) (E_S2 SetInt))
                       (let ((a!1 (= S1_2 (setunion E_S1 (set (min S1_2)))))
                             (a!2 (= E_S2 (setunion S2 (set (min E_S2)))))
                             (a!3 (not (not (forall ((ES_X SetInt))
                                              (let ((a!1 (and (>= (min E_S2)
                                                                  (+ (max ES_X)
                                                                     1))
                                                              (= ES_X
                                                                 (setminus E_S1
                                                                           E_S2)))))
                                                (not a!1))))))
                             (a!5 (and true (>= (max S1_2) (+ (min S1_2) 1))))
                             (a!6 (and true (>= (max E_S2) (+ (min E_S2) 1))))
                             (a!7 (and true (<= (min S2) (+ (max S2) 0))))
                             (a!8 (and true (<= (min E_S1) (+ (max E_S1) 0))))
                             (a!9 (forall ((x Int) (y Int))
                                    (let ((a!1 (subset (set x)
                                                       (setunion (setminus E_S1
                                                                           E_S2)
                                                                 (set (min E_S2)))))
                                          (a!2 (subset (set y)
                                                       (setunion (setminus E_S1
                                                                           E_S2)
                                                                 (set (min E_S2)))))
                                          (a!3 (forall ((z Int))
                                                 (let ((a!1 (subset (set z)
                                                                    (setunion (setminus E_S1
                                                                                        E_S2)
                                                                              (set (min E_S2))))))
                                                   (not (and a!1
                                                             (>= z (+ x 1))
                                                             (>= y (+ z 1)))))))
                                          (a!4 (not (and true (= y (+ x 1))))))
                                      (not (and a!1 a!2 (>= y (+ x 1)) a!3 a!4))))))
                       (let ((a!4 (and (not (= (setminus E_S1 E_S2) emptyset))
                                       a!3)))
                       (let ((a!10 (and a!1
                                        a!2
                                        (subset E_S2 E_S1)
                                        (not (= S2 emptyset))
                                        (not a!4)
                                        true
                                        (= (min E_S1) (+ (min S1_2) 1))
                                        true
                                        (= (min S2) (+ (min E_S2) 1))
                                        a!5
                                        a!6
                                        a!7
                                        a!8
                                        a!9)))
                         (not a!10))))))))
      (a!13 (= S3 (setunion S4 (set (min S3)))))
      (a!15 (= S3 (setunion S3_1 (set (min S3)))))
      (a!16 (= S3_1 (setunion S3_2 (set (min S3_1)))))
      (a!17 (= S3_2 (setunion S4 (set (min S3_2)))))
      (a!18 (and true (>= (max S3_2) (+ (min S3_2) 1))))
      (a!19 (and true (<= (min S4) (+ (max S4) 0))))
      (a!21 (not (not (forall ((E_S1 SetInt) (E_S2 SetInt))
                        (let ((a!1 (= S3_2 (setunion E_S1 (set (min S3_2)))))
                              (a!2 (= E_S2 (setunion S4 (set (min E_S2)))))
                              (a!3 (not (not (forall ((ES_X SetInt))
                                               (let ((a!1 (and (>= (min E_S2)
                                                                   (+ (max ES_X)
                                                                      1))
                                                               (= ES_X
                                                                  (setminus E_S1
                                                                            E_S2)))))
                                                 (not a!1))))))
                              (a!5 (and true (>= (max S3_2) (+ (min S3_2) 1))))
                              (a!6 (and true (>= (max E_S2) (+ (min E_S2) 1))))
                              (a!7 (and true (<= (min S4) (+ (max S4) 0))))
                              (a!8 (and true (<= (min E_S1) (+ (max E_S1) 0))))
                              (a!9 (forall ((x Int) (y Int))
                                     (let ((a!1 (subset (set x)
                                                        (setunion (setminus E_S1
                                                                            E_S2)
                                                                  (set (min E_S2)))))
                                           (a!2 (subset (set y)
                                                        (setunion (setminus E_S1
                                                                            E_S2)
                                                                  (set (min E_S2)))))
                                           (a!3 (forall ((z Int))
                                                  (let ((a!1 (subset (set z)
                                                                     (setunion (setminus E_S1
                                                                                         E_S2)
                                                                               (set (min E_S2))))))
                                                    (not (and a!1
                                                              (>= z (+ x 1))
                                                              (>= y (+ z 1)))))))
                                           (a!4 (not (and true (= y (+ x 1))))))
                                       (not (and a!1 a!2 (>= y (+ x 1)) a!3 a!4))))))
                        (let ((a!4 (and (not (= (setminus E_S1 E_S2) emptyset))
                                        a!3)))
                        (let ((a!10 (and a!1
                                         a!2
                                         (subset E_S2 E_S1)
                                         (not (= S4 emptyset))
                                         (not a!4)
                                         true
                                         (= (min E_S1) (+ (min S3_2) 1))
                                         true
                                         (= (min S4) (+ (min E_S2) 1))
                                         a!5
                                         a!6
                                         a!7
                                         a!8
                                         a!9)))
                          (not a!10)))))))))
(let ((a!2 (and (and |[E,0]| (>= E 1)) a!1 (= (min S2) (+ (min S1) 1))))
      (a!8 (and a!5
                true
                (= (min S2) (+ (min S1_2) 1))
                a!6
                true
                (>= (max S2) (+ (min S1_2) 1))
                true
                (<= (min S2) (+ (max S1_2) 0))
                a!7
                true
                (= (max S1_2) (+ (max S2) 0))))
      (a!14 (and (and |[E1,1]| (>= E1 1)) a!13 (= (min S4) (+ (min S3) 1))))
      (a!20 (and a!17
                 true
                 (= (min S4) (+ (min S3_2) 1))
                 a!18
                 true
                 (>= (max S4) (+ (min S3_2) 1))
                 true
                 (<= (min S4) (+ (max S3_2) 0))
                 a!19
                 true
                 (= (max S3_2) (+ (max S4) 0)))))
(let ((a!10 (not (and (not (= S1_2 S2)) (not a!8) a!9)))
      (a!22 (not (and (not (= S3_2 S4)) (not a!20) a!21))))
(let ((a!11 (and (and |[E,0]| (>= E 1))
                 a!3
                 (= (min S1_1) (+ (min S1) 1))
                 a!4
                 (= (min S1_2) (+ (min S1_1) 1))
                 a!10))
      (a!23 (and (and |[E1,1]| (>= E1 1))
                 a!15
                 (= (min S3_1) (+ (min S3) 1))
                 a!16
                 (= (min S3_2) (+ (min S3_1) 1))
                 a!22)))
(let ((a!12 (and (not (and (not |[E,0]|) (= E F) (= S1 S2)))
                 (not a!2)
                 (not a!11)))
      (a!24 (and (not (and (not |[E1,1]|) (= E1 F1) (= S3 S4)))
                 (not a!14)
                 (not a!23))))
  (and (= (min S2) (+ (min S1) 4))
       (= (- (min S1) (max S3)) 1)
       (= (min S4) (+ (min S3) 5))
       (= (- (max S2) (min S2)) 1)
       (= (max S4) (+ (min S4) 1))
       (not a!12)
       (not a!24)
       true
       (not (and (= E E1) |[E,0]| |[E1,1]|))))))))
