(let ((a!1 (or false
               (and (= (max S1_plus) 0) (= (min S2_minus) 5))
               (and (= (max S1_plus) 1) (= (min S2_minus) 4))
               (and (= (max S1_plus) 2) (= (min S2_minus) 3))
               (and (= (max S1_plus) 3) (= (min S2_minus) 2))
               (and (= (max S1_plus) 4) (= (min S2_minus) 1))
               (and (= (max S1_plus) 5) (= (min S2_minus) 0))))
      (a!2 (and (and (= S1_plus emptyset) (= S2_plus emptyset))
                (= (min S2_minus) (+ (min S1_minus) 5))))
      (a!4 (not (and (not |[E,0]|)
                     (= E_plus (+ F_plus 0))
                     (= S1_minus S2_minus)
                     (= S1_plus S2_plus))))
      (a!5 (= S1_plus (setunion S2_plus (set (max S1_plus)))))
      (a!6 (or false
               (and (= (max S1_plus) 0) (= (min S2_minus) 1))
               (and (= (max S1_plus) 1) (= (min S2_minus) 0))))
      (a!7 (and (and (= S1_plus emptyset) (= S2_plus emptyset))
                (= (min S2_minus) (+ (min S1_minus) 1))))
      (a!10 (= S1_plus (setunion S1_1_plus (set (max S1_plus)))))
      (a!11 (or false
                (and (= (max S1_plus) 0) (= (min S1_1_minus) 1))
                (and (= (max S1_plus) 1) (= (min S1_1_minus) 0))))
      (a!12 (and (= S1_plus emptyset)
                 (= S1_1_plus emptyset)
                 (= (min S1_1_minus) (+ (min S1_minus) 1))))
      (a!14 (= S1_1_plus (setunion S1_2_plus (set (max S1_1_plus)))))
      (a!15 (or false
                (and (= (max S1_1_plus) 0) (= (min S1_2_minus) 1))
                (and (= (max S1_1_plus) 1) (= (min S1_2_minus) 0))))
      (a!16 (and (= S1_1_plus emptyset)
                 (= S1_2_plus emptyset)
                 (= (min S1_2_minus) (+ (min S1_1_minus) 1))))
      (a!18 (= S1_2_plus (setunion S2_plus (set (max S1_2_plus)))))
      (a!19 (and (= S1_2_minus emptyset)
                 (= S2_minus emptyset)
                 (<= (min S1_2_plus) (+ (min S2_plus) 0))))
      (a!20 (or false (and (<= (min S1_2_plus) 0) (<= (max S2_minus) 0))))
      (a!22 (and (= S2_minus emptyset)
                 (= S1_2_minus emptyset)
                 (<= (min S2_plus) (+ (min S1_2_plus) 0))))
      (a!23 (or false (and (<= (min S2_plus) 0) (<= (max S1_2_minus) 0))))
      (a!25 (and (= S1_2_minus emptyset)
                 (>= (max S1_2_plus) (+ (min S1_2_plus) 1))))
      (a!26 (and (= S1_2_plus emptyset)
                 (>= (max S1_2_minus) (+ (min S1_2_minus) 1))))
      (a!28 (and (= S1_2_minus emptyset)
                 (<= (min S1_2_plus) (+ (max S2_plus) 0))))
      (a!29 (or false (and (<= (min S1_2_plus) 0) (<= (min S2_minus) 0))))
      (a!30 (and (= S2_plus emptyset)
                 (<= (min S2_minus) (+ (max S1_2_minus) 0))))
      (a!31 (and (= S2_minus emptyset) (>= (max S1_2_plus) (+ (min S2_plus) 1))))
      (a!32 (and (= S1_2_plus emptyset)
                 (>= (max S2_minus) (+ (min S1_2_minus) 1))))
      (a!34 (and (= S2_minus emptyset) (<= (min S2_plus) (+ (max S2_plus) 0))))
      (a!35 (or false (and (<= (min S2_plus) 0) (<= (min S2_minus) 0))))
      (a!36 (and (= S2_plus emptyset) (<= (min S2_minus) (+ (max S2_minus) 0))))
      (a!38 (or false
                (and (<= (max S1_2_plus) 0) (<= (min S2_minus) 1))
                (and (<= (max S1_2_plus) 1) (<= (min S2_minus) 0))))
      (a!39 (and (and (= S1_2_plus emptyset) (= S2_plus emptyset))
                 (<= (min S2_minus) (+ (min S1_2_minus) 1))))
      (a!41 (or false
                (and (>= (max S1_2_plus) 0) (>= (min S2_minus) 1))
                (and (>= (max S1_2_plus) 1) (>= (min S2_minus) 0))))
      (a!42 (and (and (= S1_2_plus emptyset) (= S2_plus emptyset))
                 (>= (min S2_minus) (+ (min S1_2_minus) 1))))
      (a!45 (not (forall ((E_S2_plus SetInt)
                          (E_S2_minus SetInt)
                          (E_S1_plus SetInt)
                          (E_S1_minus SetInt))
                   (let ((a!1 (= S1_2_plus
                                 (setunion E_S1_plus (set (max S1_2_plus)))))
                         (a!2 (= E_S2_plus
                                 (setunion S2_plus (set (max E_S2_plus)))))
                         (a!3 (not (and (= (setminus emptyset emptyset)
                                           emptyset)
                                        (= (setminus E_S1_plus E_S2_plus)
                                           emptyset))))
                         (a!4 (not (forall ((ES_X_plus SetInt)
                                            (ES_X_minus SetInt))
                                     (let ((a!1 (and (= emptyset emptyset)
                                                     (>= (min ES_X_plus)
                                                         (+ (max E_S2_plus) 1))))
                                           (a!2 (or false
                                                    (and (>= (min ES_X_plus) 0)
                                                         (>= (min emptyset) 1))
                                                    (and (>= (min ES_X_plus) 1)
                                                         (>= (min emptyset) 0))))
                                           (a!3 (and (= E_S2_plus emptyset)
                                                     (>= (min emptyset)
                                                         (+ (max emptyset) 1))))
                                           (a!7 (and (= ES_X_minus emptyset)
                                                     (>= (min emptyset)
                                                         (+ (max E_S2_plus) 1))))
                                           (a!8 (or false
                                                    (and (>= (min emptyset) 0)
                                                         (>= (min emptyset) 1))
                                                    (and (>= (min emptyset) 1)
                                                         (>= (min emptyset) 0))))
                                           (a!9 (and (= E_S2_plus emptyset)
                                                     (>= (min emptyset)
                                                         (+ (max ES_X_minus) 1))))
                                           (a!13 (and (= ES_X_minus emptyset)
                                                      (>= (min ES_X_plus)
                                                          (+ (max E_S2_plus) 1))))
                                           (a!17 (and (= emptyset emptyset)
                                                      (>= (min emptyset)
                                                          (+ (max E_S2_plus) 1)))))
                                     (let ((a!4 (or a!1
                                                    (and (and (= emptyset
                                                                 emptyset)
                                                              (= E_S2_plus
                                                                 emptyset))
                                                         a!2)
                                                    a!3))
                                           (a!10 (or a!7
                                                     (and (and (= ES_X_minus
                                                                  emptyset)
                                                               (= E_S2_plus
                                                                  emptyset))
                                                          a!8)
                                                     a!9))
                                           (a!14 (or a!13
                                                     (and (and (= ES_X_minus
                                                                  emptyset)
                                                               (= E_S2_plus
                                                                  emptyset))
                                                          a!2)
                                                     a!9))
                                           (a!18 (or a!17
                                                     (and (and (= emptyset
                                                                  emptyset)
                                                               (= E_S2_plus
                                                                  emptyset))
                                                          a!8)
                                                     a!3)))
                                     (let ((a!5 (not (and a!4
                                                          (= emptyset
                                                             (setminus emptyset
                                                                       emptyset))
                                                          (= ES_X_plus
                                                             (setminus E_S1_plus
                                                                       E_S2_plus)))))
                                           (a!11 (not (and a!10
                                                           (= ES_X_minus
                                                              (setminus emptyset
                                                                        emptyset))
                                                           (= emptyset
                                                              (setminus E_S1_plus
                                                                        E_S2_plus)))))
                                           (a!15 (not (and a!14
                                                           (= ES_X_minus
                                                              (setminus emptyset
                                                                        emptyset))
                                                           (= ES_X_plus
                                                              (setminus E_S1_plus
                                                                        E_S2_plus)))))
                                           (a!19 (not (and a!18
                                                           (= emptyset
                                                              (setminus emptyset
                                                                        emptyset))
                                                           (= emptyset
                                                              (setminus E_S1_plus
                                                                        E_S2_plus))))))
                                     (let ((a!6 (and (and true
                                                          (and (distinct ES_X_plus
                                                                         emptyset)
                                                               (= ES_X_minus
                                                                  emptyset)))
                                                     (not a!5)))
                                           (a!12 (and (and true
                                                           (and (= ES_X_plus
                                                                   emptyset)
                                                                (distinct ES_X_minus
                                                                          emptyset)))
                                                      (not a!11)))
                                           (a!16 (and (and true
                                                           (and (distinct ES_X_plus
                                                                          emptyset)
                                                                (distinct ES_X_minus
                                                                          emptyset)))
                                                      (not a!15)))
                                           (a!20 (and (and true
                                                           (and (= ES_X_plus
                                                                   emptyset)
                                                                (= ES_X_minus
                                                                   emptyset)))
                                                      (not a!19))))
                                       (and (not a!6)
                                            (not a!12)
                                            (not a!16)
                                            (not a!20)))))))))
                         (a!5 (or false
                                  (and (<= (max S1_2_plus) 0)
                                       (<= (min emptyset) 1))
                                  (and (<= (max S1_2_plus) 1)
                                       (<= (min emptyset) 0))))
                         (a!6 (and (and (= S1_2_plus emptyset)
                                        (distinct S1_2_minus emptyset))
                                   (distinct E_S1_plus emptyset)))
                         (a!7 (and (and (= S1_2_plus emptyset)
                                        (= E_S1_plus emptyset))
                                   (<= (min emptyset) (+ (min S1_2_minus) 1))))
                         (a!9 (or false
                                  (and (>= (max S1_2_plus) 0)
                                       (>= (min emptyset) 1))
                                  (and (>= (max S1_2_plus) 1)
                                       (>= (min emptyset) 0))))
                         (a!10 (and (and (= S1_2_plus emptyset)
                                         (= E_S1_plus emptyset))
                                    (>= (min emptyset) (+ (min S1_2_minus) 1))))
                         (a!12 (or false
                                   (and (<= (max E_S2_plus) 0)
                                        (<= (min S2_minus) 1))
                                   (and (<= (max E_S2_plus) 1)
                                        (<= (min S2_minus) 0))))
                         (a!14 (and (and (= E_S2_plus emptyset)
                                         (= S2_plus emptyset))
                                    (<= (min S2_minus) (+ (min emptyset) 1))))
                         (a!15 (or false
                                   (and (>= (max E_S2_plus) 0)
                                        (>= (min S2_minus) 1))
                                   (and (>= (max E_S2_plus) 1)
                                        (>= (min S2_minus) 0))))
                         (a!17 (and (and (= E_S2_plus emptyset)
                                         (= S2_plus emptyset))
                                    (>= (min S2_minus) (+ (min emptyset) 1))))
                         (a!19 (and (= S1_2_minus emptyset)
                                    (>= (max S1_2_plus) (+ (min S1_2_plus) 1))))
                         (a!20 (and (= S1_2_plus emptyset)
                                    (>= (max S1_2_minus) (+ (min S1_2_minus) 1))))
                         (a!22 (and (= emptyset emptyset)
                                    (>= (max E_S2_plus) (+ (min E_S2_plus) 1))))
                         (a!23 (and (= E_S2_plus emptyset)
                                    (>= (max emptyset) (+ (min emptyset) 1))))
                         (a!25 (and (= S2_minus emptyset)
                                    (<= (min S2_plus) (+ (max S2_plus) 0))))
                         (a!26 (or false
                                   (and (<= (min S2_plus) 0)
                                        (<= (min S2_minus) 0))))
                         (a!27 (and (= S2_plus emptyset)
                                    (<= (min S2_minus) (+ (max S2_minus) 0))))
                         (a!29 (and (= emptyset emptyset)
                                    (<= (min E_S1_plus) (+ (max E_S1_plus) 0))))
                         (a!30 (or false
                                   (and (<= (min E_S1_plus) 0)
                                        (<= (min emptyset) 0))))
                         (a!31 (and (= E_S1_plus emptyset)
                                    (<= (min emptyset) (+ (max emptyset) 0))))
                         (a!35 (= S1_2_plus
                                  (setunion emptyset (set (max S1_2_plus)))))
                         (a!36 (not (and (= (setminus E_S1_minus emptyset)
                                            emptyset)
                                         (= (setminus emptyset E_S2_plus)
                                            emptyset))))
                         (a!37 (not (forall ((ES_X_plus SetInt)
                                             (ES_X_minus SetInt))
                                      (let ((a!1 (and (= emptyset emptyset)
                                                      (>= (min ES_X_plus)
                                                          (+ (max E_S2_plus) 1))))
                                            (a!2 (or false
                                                     (and (>= (min ES_X_plus) 0)
                                                          (>= (min emptyset) 1))
                                                     (and (>= (min ES_X_plus) 1)
                                                          (>= (min emptyset) 0))))
                                            (a!3 (and (= E_S2_plus emptyset)
                                                      (>= (min emptyset)
                                                          (+ (max emptyset) 1))))
                                            (a!7 (and (= ES_X_minus emptyset)
                                                      (>= (min emptyset)
                                                          (+ (max E_S2_plus) 1))))
                                            (a!8 (or false
                                                     (and (>= (min emptyset) 0)
                                                          (>= (min emptyset) 1))
                                                     (and (>= (min emptyset) 1)
                                                          (>= (min emptyset) 0))))
                                            (a!9 (and (= E_S2_plus emptyset)
                                                      (>= (min emptyset)
                                                          (+ (max ES_X_minus) 1))))
                                            (a!13 (and (= ES_X_minus emptyset)
                                                       (>= (min ES_X_plus)
                                                           (+ (max E_S2_plus) 1))))
                                            (a!17 (and (= emptyset emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max E_S2_plus) 1)))))
                                      (let ((a!4 (or a!1
                                                     (and (and (= emptyset
                                                                  emptyset)
                                                               (= E_S2_plus
                                                                  emptyset))
                                                          a!2)
                                                     a!3))
                                            (a!10 (or a!7
                                                      (and (and (= ES_X_minus
                                                                   emptyset)
                                                                (= E_S2_plus
                                                                   emptyset))
                                                           a!8)
                                                      a!9))
                                            (a!14 (or a!13
                                                      (and (and (= ES_X_minus
                                                                   emptyset)
                                                                (= E_S2_plus
                                                                   emptyset))
                                                           a!2)
                                                      a!9))
                                            (a!18 (or a!17
                                                      (and (and (= emptyset
                                                                   emptyset)
                                                                (= E_S2_plus
                                                                   emptyset))
                                                           a!8)
                                                      a!3)))
                                      (let ((a!5 (not (and a!4
                                                           (= emptyset
                                                              (setminus E_S1_minus
                                                                        emptyset))
                                                           (= ES_X_plus
                                                              (setminus emptyset
                                                                        E_S2_plus)))))
                                            (a!11 (not (and a!10
                                                            (= ES_X_minus
                                                               (setminus E_S1_minus
                                                                         emptyset))
                                                            (= emptyset
                                                               (setminus emptyset
                                                                         E_S2_plus)))))
                                            (a!15 (not (and a!14
                                                            (= ES_X_minus
                                                               (setminus E_S1_minus
                                                                         emptyset))
                                                            (= ES_X_plus
                                                               (setminus emptyset
                                                                         E_S2_plus)))))
                                            (a!19 (not (and a!18
                                                            (= emptyset
                                                               (setminus E_S1_minus
                                                                         emptyset))
                                                            (= emptyset
                                                               (setminus emptyset
                                                                         E_S2_plus))))))
                                      (let ((a!6 (and (and true
                                                           (and (distinct ES_X_plus
                                                                          emptyset)
                                                                (= ES_X_minus
                                                                   emptyset)))
                                                      (not a!5)))
                                            (a!12 (and (and true
                                                            (and (= ES_X_plus
                                                                    emptyset)
                                                                 (distinct ES_X_minus
                                                                           emptyset)))
                                                       (not a!11)))
                                            (a!16 (and (and true
                                                            (and (distinct ES_X_plus
                                                                           emptyset)
                                                                 (distinct ES_X_minus
                                                                           emptyset)))
                                                       (not a!15)))
                                            (a!20 (and (and true
                                                            (and (= ES_X_plus
                                                                    emptyset)
                                                                 (= ES_X_minus
                                                                    emptyset)))
                                                       (not a!19))))
                                        (and (not a!6)
                                             (not a!12)
                                             (not a!16)
                                             (not a!20)))))))))
                         (a!38 (or false
                                   (and (<= (max S1_2_plus) 0)
                                        (<= (min E_S1_minus) 1))
                                   (and (<= (max S1_2_plus) 1)
                                        (<= (min E_S1_minus) 0))))
                         (a!39 (and (and (= S1_2_plus emptyset)
                                         (distinct S1_2_minus emptyset))
                                    (distinct emptyset emptyset)))
                         (a!40 (and (and (= S1_2_plus emptyset)
                                         (= emptyset emptyset))
                                    (<= (min E_S1_minus) (+ (min S1_2_minus) 1))))
                         (a!42 (or false
                                   (and (>= (max S1_2_plus) 0)
                                        (>= (min E_S1_minus) 1))
                                   (and (>= (max S1_2_plus) 1)
                                        (>= (min E_S1_minus) 0))))
                         (a!43 (and (and (= S1_2_plus emptyset)
                                         (= emptyset emptyset))
                                    (>= (min E_S1_minus) (+ (min S1_2_minus) 1))))
                         (a!45 (and (= E_S1_minus emptyset)
                                    (<= (min emptyset) (+ (max emptyset) 0))))
                         (a!46 (or false
                                   (and (<= (min emptyset) 0)
                                        (<= (min E_S1_minus) 0))))
                         (a!47 (and (= emptyset emptyset)
                                    (<= (min E_S1_minus) (+ (max E_S1_minus) 0))))
                         (a!51 (not (and (= (setminus E_S1_minus emptyset)
                                            emptyset)
                                         (= (setminus E_S1_plus E_S2_plus)
                                            emptyset))))
                         (a!52 (not (forall ((ES_X_plus SetInt)
                                             (ES_X_minus SetInt))
                                      (let ((a!1 (and (= emptyset emptyset)
                                                      (>= (min ES_X_plus)
                                                          (+ (max E_S2_plus) 1))))
                                            (a!2 (or false
                                                     (and (>= (min ES_X_plus) 0)
                                                          (>= (min emptyset) 1))
                                                     (and (>= (min ES_X_plus) 1)
                                                          (>= (min emptyset) 0))))
                                            (a!3 (and (= E_S2_plus emptyset)
                                                      (>= (min emptyset)
                                                          (+ (max emptyset) 1))))
                                            (a!7 (and (= ES_X_minus emptyset)
                                                      (>= (min emptyset)
                                                          (+ (max E_S2_plus) 1))))
                                            (a!8 (or false
                                                     (and (>= (min emptyset) 0)
                                                          (>= (min emptyset) 1))
                                                     (and (>= (min emptyset) 1)
                                                          (>= (min emptyset) 0))))
                                            (a!9 (and (= E_S2_plus emptyset)
                                                      (>= (min emptyset)
                                                          (+ (max ES_X_minus) 1))))
                                            (a!13 (and (= ES_X_minus emptyset)
                                                       (>= (min ES_X_plus)
                                                           (+ (max E_S2_plus) 1))))
                                            (a!17 (and (= emptyset emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max E_S2_plus) 1)))))
                                      (let ((a!4 (or a!1
                                                     (and (and (= emptyset
                                                                  emptyset)
                                                               (= E_S2_plus
                                                                  emptyset))
                                                          a!2)
                                                     a!3))
                                            (a!10 (or a!7
                                                      (and (and (= ES_X_minus
                                                                   emptyset)
                                                                (= E_S2_plus
                                                                   emptyset))
                                                           a!8)
                                                      a!9))
                                            (a!14 (or a!13
                                                      (and (and (= ES_X_minus
                                                                   emptyset)
                                                                (= E_S2_plus
                                                                   emptyset))
                                                           a!2)
                                                      a!9))
                                            (a!18 (or a!17
                                                      (and (and (= emptyset
                                                                   emptyset)
                                                                (= E_S2_plus
                                                                   emptyset))
                                                           a!8)
                                                      a!3)))
                                      (let ((a!5 (not (and a!4
                                                           (= emptyset
                                                              (setminus E_S1_minus
                                                                        emptyset))
                                                           (= ES_X_plus
                                                              (setminus E_S1_plus
                                                                        E_S2_plus)))))
                                            (a!11 (not (and a!10
                                                            (= ES_X_minus
                                                               (setminus E_S1_minus
                                                                         emptyset))
                                                            (= emptyset
                                                               (setminus E_S1_plus
                                                                         E_S2_plus)))))
                                            (a!15 (not (and a!14
                                                            (= ES_X_minus
                                                               (setminus E_S1_minus
                                                                         emptyset))
                                                            (= ES_X_plus
                                                               (setminus E_S1_plus
                                                                         E_S2_plus)))))
                                            (a!19 (not (and a!18
                                                            (= emptyset
                                                               (setminus E_S1_minus
                                                                         emptyset))
                                                            (= emptyset
                                                               (setminus E_S1_plus
                                                                         E_S2_plus))))))
                                      (let ((a!6 (and (and true
                                                           (and (distinct ES_X_plus
                                                                          emptyset)
                                                                (= ES_X_minus
                                                                   emptyset)))
                                                      (not a!5)))
                                            (a!12 (and (and true
                                                            (and (= ES_X_plus
                                                                    emptyset)
                                                                 (distinct ES_X_minus
                                                                           emptyset)))
                                                       (not a!11)))
                                            (a!16 (and (and true
                                                            (and (distinct ES_X_plus
                                                                           emptyset)
                                                                 (distinct ES_X_minus
                                                                           emptyset)))
                                                       (not a!15)))
                                            (a!20 (and (and true
                                                            (and (= ES_X_plus
                                                                    emptyset)
                                                                 (= ES_X_minus
                                                                    emptyset)))
                                                       (not a!19))))
                                        (and (not a!6)
                                             (not a!12)
                                             (not a!16)
                                             (not a!20)))))))))
                         (a!53 (and (and (= S1_2_plus emptyset)
                                         (= E_S1_plus emptyset))
                                    (<= (min E_S1_minus) (+ (min S1_2_minus) 1))))
                         (a!55 (and (and (= S1_2_plus emptyset)
                                         (= E_S1_plus emptyset))
                                    (>= (min E_S1_minus) (+ (min S1_2_minus) 1))))
                         (a!57 (and (= E_S1_minus emptyset)
                                    (<= (min E_S1_plus) (+ (max E_S1_plus) 0))))
                         (a!58 (or false
                                   (and (<= (min E_S1_plus) 0)
                                        (<= (min E_S1_minus) 0))))
                         (a!59 (and (= E_S1_plus emptyset)
                                    (<= (min E_S1_minus) (+ (max E_S1_minus) 0))))
                         (a!63 (not (and (= (setminus emptyset emptyset)
                                            emptyset)
                                         (= (setminus emptyset E_S2_plus)
                                            emptyset))))
                         (a!64 (not (forall ((ES_X_plus SetInt)
                                             (ES_X_minus SetInt))
                                      (let ((a!1 (and (= emptyset emptyset)
                                                      (>= (min ES_X_plus)
                                                          (+ (max E_S2_plus) 1))))
                                            (a!2 (or false
                                                     (and (>= (min ES_X_plus) 0)
                                                          (>= (min emptyset) 1))
                                                     (and (>= (min ES_X_plus) 1)
                                                          (>= (min emptyset) 0))))
                                            (a!3 (and (= E_S2_plus emptyset)
                                                      (>= (min emptyset)
                                                          (+ (max emptyset) 1))))
                                            (a!7 (and (= ES_X_minus emptyset)
                                                      (>= (min emptyset)
                                                          (+ (max E_S2_plus) 1))))
                                            (a!8 (or false
                                                     (and (>= (min emptyset) 0)
                                                          (>= (min emptyset) 1))
                                                     (and (>= (min emptyset) 1)
                                                          (>= (min emptyset) 0))))
                                            (a!9 (and (= E_S2_plus emptyset)
                                                      (>= (min emptyset)
                                                          (+ (max ES_X_minus) 1))))
                                            (a!13 (and (= ES_X_minus emptyset)
                                                       (>= (min ES_X_plus)
                                                           (+ (max E_S2_plus) 1))))
                                            (a!17 (and (= emptyset emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max E_S2_plus) 1)))))
                                      (let ((a!4 (or a!1
                                                     (and (and (= emptyset
                                                                  emptyset)
                                                               (= E_S2_plus
                                                                  emptyset))
                                                          a!2)
                                                     a!3))
                                            (a!10 (or a!7
                                                      (and (and (= ES_X_minus
                                                                   emptyset)
                                                                (= E_S2_plus
                                                                   emptyset))
                                                           a!8)
                                                      a!9))
                                            (a!14 (or a!13
                                                      (and (and (= ES_X_minus
                                                                   emptyset)
                                                                (= E_S2_plus
                                                                   emptyset))
                                                           a!2)
                                                      a!9))
                                            (a!18 (or a!17
                                                      (and (and (= emptyset
                                                                   emptyset)
                                                                (= E_S2_plus
                                                                   emptyset))
                                                           a!8)
                                                      a!3)))
                                      (let ((a!5 (not (and a!4
                                                           (= emptyset
                                                              (setminus emptyset
                                                                        emptyset))
                                                           (= ES_X_plus
                                                              (setminus emptyset
                                                                        E_S2_plus)))))
                                            (a!11 (not (and a!10
                                                            (= ES_X_minus
                                                               (setminus emptyset
                                                                         emptyset))
                                                            (= emptyset
                                                               (setminus emptyset
                                                                         E_S2_plus)))))
                                            (a!15 (not (and a!14
                                                            (= ES_X_minus
                                                               (setminus emptyset
                                                                         emptyset))
                                                            (= ES_X_plus
                                                               (setminus emptyset
                                                                         E_S2_plus)))))
                                            (a!19 (not (and a!18
                                                            (= emptyset
                                                               (setminus emptyset
                                                                         emptyset))
                                                            (= emptyset
                                                               (setminus emptyset
                                                                         E_S2_plus))))))
                                      (let ((a!6 (and (and true
                                                           (and (distinct ES_X_plus
                                                                          emptyset)
                                                                (= ES_X_minus
                                                                   emptyset)))
                                                      (not a!5)))
                                            (a!12 (and (and true
                                                            (and (= ES_X_plus
                                                                    emptyset)
                                                                 (distinct ES_X_minus
                                                                           emptyset)))
                                                       (not a!11)))
                                            (a!16 (and (and true
                                                            (and (distinct ES_X_plus
                                                                           emptyset)
                                                                 (distinct ES_X_minus
                                                                           emptyset)))
                                                       (not a!15)))
                                            (a!20 (and (and true
                                                            (and (= ES_X_plus
                                                                    emptyset)
                                                                 (= ES_X_minus
                                                                    emptyset)))
                                                       (not a!19))))
                                        (and (not a!6)
                                             (not a!12)
                                             (not a!16)
                                             (not a!20)))))))))
                         (a!65 (and (and (= S1_2_plus emptyset)
                                         (= emptyset emptyset))
                                    (<= (min emptyset) (+ (min S1_2_minus) 1))))
                         (a!67 (and (and (= S1_2_plus emptyset)
                                         (= emptyset emptyset))
                                    (>= (min emptyset) (+ (min S1_2_minus) 1))))
                         (a!69 (and (= emptyset emptyset)
                                    (<= (min emptyset) (+ (max emptyset) 0))))
                         (a!70 (or false
                                   (and (<= (min emptyset) 0)
                                        (<= (min emptyset) 0))))
                         (a!74 (= E_S2_minus
                                  (setunion S2_minus (set (min E_S2_minus)))))
                         (a!75 (not (and (= (setminus emptyset E_S2_minus)
                                            emptyset)
                                         (= (setminus E_S1_plus emptyset)
                                            emptyset))))
                         (a!76 (not (forall ((ES_X_plus SetInt)
                                             (ES_X_minus SetInt))
                                      (let ((a!1 (and (= emptyset emptyset)
                                                      (>= (min ES_X_plus)
                                                          (+ (max emptyset) 1))))
                                            (a!2 (or false
                                                     (and (>= (min ES_X_plus) 0)
                                                          (>= (min E_S2_minus)
                                                              1))
                                                     (and (>= (min ES_X_plus) 1)
                                                          (>= (min E_S2_minus)
                                                              0))))
                                            (a!3 (and (= emptyset emptyset)
                                                      (>= (min E_S2_minus)
                                                          (+ (max emptyset) 1))))
                                            (a!7 (and (= ES_X_minus emptyset)
                                                      (>= (min emptyset)
                                                          (+ (max emptyset) 1))))
                                            (a!8 (or false
                                                     (and (>= (min emptyset) 0)
                                                          (>= (min E_S2_minus)
                                                              1))
                                                     (and (>= (min emptyset) 1)
                                                          (>= (min E_S2_minus)
                                                              0))))
                                            (a!9 (and (= emptyset emptyset)
                                                      (>= (min E_S2_minus)
                                                          (+ (max ES_X_minus) 1))))
                                            (a!13 (and (= ES_X_minus emptyset)
                                                       (>= (min ES_X_plus)
                                                           (+ (max emptyset) 1))))
                                            (a!17 (and (= emptyset emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max emptyset) 1)))))
                                      (let ((a!4 (or a!1
                                                     (and (and (= emptyset
                                                                  emptyset)
                                                               (= emptyset
                                                                  emptyset))
                                                          a!2)
                                                     a!3))
                                            (a!10 (or a!7
                                                      (and (and (= ES_X_minus
                                                                   emptyset)
                                                                (= emptyset
                                                                   emptyset))
                                                           a!8)
                                                      a!9))
                                            (a!14 (or a!13
                                                      (and (and (= ES_X_minus
                                                                   emptyset)
                                                                (= emptyset
                                                                   emptyset))
                                                           a!2)
                                                      a!9))
                                            (a!18 (or a!17
                                                      (and (and (= emptyset
                                                                   emptyset)
                                                                (= emptyset
                                                                   emptyset))
                                                           a!8)
                                                      a!3)))
                                      (let ((a!5 (not (and a!4
                                                           (= emptyset
                                                              (setminus emptyset
                                                                        E_S2_minus))
                                                           (= ES_X_plus
                                                              (setminus E_S1_plus
                                                                        emptyset)))))
                                            (a!11 (not (and a!10
                                                            (= ES_X_minus
                                                               (setminus emptyset
                                                                         E_S2_minus))
                                                            (= emptyset
                                                               (setminus E_S1_plus
                                                                         emptyset)))))
                                            (a!15 (not (and a!14
                                                            (= ES_X_minus
                                                               (setminus emptyset
                                                                         E_S2_minus))
                                                            (= ES_X_plus
                                                               (setminus E_S1_plus
                                                                         emptyset)))))
                                            (a!19 (not (and a!18
                                                            (= emptyset
                                                               (setminus emptyset
                                                                         E_S2_minus))
                                                            (= emptyset
                                                               (setminus E_S1_plus
                                                                         emptyset))))))
                                      (let ((a!6 (and (and true
                                                           (and (distinct ES_X_plus
                                                                          emptyset)
                                                                (= ES_X_minus
                                                                   emptyset)))
                                                      (not a!5)))
                                            (a!12 (and (and true
                                                            (and (= ES_X_plus
                                                                    emptyset)
                                                                 (distinct ES_X_minus
                                                                           emptyset)))
                                                       (not a!11)))
                                            (a!16 (and (and true
                                                            (and (distinct ES_X_plus
                                                                           emptyset)
                                                                 (distinct ES_X_minus
                                                                           emptyset)))
                                                       (not a!15)))
                                            (a!20 (and (and true
                                                            (and (= ES_X_plus
                                                                    emptyset)
                                                                 (= ES_X_minus
                                                                    emptyset)))
                                                       (not a!19))))
                                        (and (not a!6)
                                             (not a!12)
                                             (not a!16)
                                             (not a!20)))))))))
                         (a!77 (or false
                                   (and (<= (max emptyset) 0)
                                        (<= (min S2_minus) 1))
                                   (and (<= (max emptyset) 1)
                                        (<= (min S2_minus) 0))))
                         (a!79 (and (and (= emptyset emptyset)
                                         (= S2_plus emptyset))
                                    (<= (min S2_minus) (+ (min E_S2_minus) 1))))
                         (a!80 (or false
                                   (and (>= (max emptyset) 0)
                                        (>= (min S2_minus) 1))
                                   (and (>= (max emptyset) 1)
                                        (>= (min S2_minus) 0))))
                         (a!82 (and (and (= emptyset emptyset)
                                         (= S2_plus emptyset))
                                    (>= (min S2_minus) (+ (min E_S2_minus) 1))))
                         (a!84 (and (= E_S2_minus emptyset)
                                    (>= (max emptyset) (+ (min emptyset) 1))))
                         (a!85 (and (= emptyset emptyset)
                                    (>= (max E_S2_minus) (+ (min E_S2_minus) 1))))
                         (a!89 (not (and (= (setminus E_S1_minus E_S2_minus)
                                            emptyset)
                                         (= (setminus emptyset emptyset)
                                            emptyset))))
                         (a!90 (not (forall ((ES_X_plus SetInt)
                                             (ES_X_minus SetInt))
                                      (let ((a!1 (and (= emptyset emptyset)
                                                      (>= (min ES_X_plus)
                                                          (+ (max emptyset) 1))))
                                            (a!2 (or false
                                                     (and (>= (min ES_X_plus) 0)
                                                          (>= (min E_S2_minus)
                                                              1))
                                                     (and (>= (min ES_X_plus) 1)
                                                          (>= (min E_S2_minus)
                                                              0))))
                                            (a!3 (and (= emptyset emptyset)
                                                      (>= (min E_S2_minus)
                                                          (+ (max emptyset) 1))))
                                            (a!7 (and (= ES_X_minus emptyset)
                                                      (>= (min emptyset)
                                                          (+ (max emptyset) 1))))
                                            (a!8 (or false
                                                     (and (>= (min emptyset) 0)
                                                          (>= (min E_S2_minus)
                                                              1))
                                                     (and (>= (min emptyset) 1)
                                                          (>= (min E_S2_minus)
                                                              0))))
                                            (a!9 (and (= emptyset emptyset)
                                                      (>= (min E_S2_minus)
                                                          (+ (max ES_X_minus) 1))))
                                            (a!13 (and (= ES_X_minus emptyset)
                                                       (>= (min ES_X_plus)
                                                           (+ (max emptyset) 1))))
                                            (a!17 (and (= emptyset emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max emptyset) 1)))))
                                      (let ((a!4 (or a!1
                                                     (and (and (= emptyset
                                                                  emptyset)
                                                               (= emptyset
                                                                  emptyset))
                                                          a!2)
                                                     a!3))
                                            (a!10 (or a!7
                                                      (and (and (= ES_X_minus
                                                                   emptyset)
                                                                (= emptyset
                                                                   emptyset))
                                                           a!8)
                                                      a!9))
                                            (a!14 (or a!13
                                                      (and (and (= ES_X_minus
                                                                   emptyset)
                                                                (= emptyset
                                                                   emptyset))
                                                           a!2)
                                                      a!9))
                                            (a!18 (or a!17
                                                      (and (and (= emptyset
                                                                   emptyset)
                                                                (= emptyset
                                                                   emptyset))
                                                           a!8)
                                                      a!3)))
                                      (let ((a!5 (not (and a!4
                                                           (= emptyset
                                                              (setminus E_S1_minus
                                                                        E_S2_minus))
                                                           (= ES_X_plus
                                                              (setminus emptyset
                                                                        emptyset)))))
                                            (a!11 (not (and a!10
                                                            (= ES_X_minus
                                                               (setminus E_S1_minus
                                                                         E_S2_minus))
                                                            (= emptyset
                                                               (setminus emptyset
                                                                         emptyset)))))
                                            (a!15 (not (and a!14
                                                            (= ES_X_minus
                                                               (setminus E_S1_minus
                                                                         E_S2_minus))
                                                            (= ES_X_plus
                                                               (setminus emptyset
                                                                         emptyset)))))
                                            (a!19 (not (and a!18
                                                            (= emptyset
                                                               (setminus E_S1_minus
                                                                         E_S2_minus))
                                                            (= emptyset
                                                               (setminus emptyset
                                                                         emptyset))))))
                                      (let ((a!6 (and (and true
                                                           (and (distinct ES_X_plus
                                                                          emptyset)
                                                                (= ES_X_minus
                                                                   emptyset)))
                                                      (not a!5)))
                                            (a!12 (and (and true
                                                            (and (= ES_X_plus
                                                                    emptyset)
                                                                 (distinct ES_X_minus
                                                                           emptyset)))
                                                       (not a!11)))
                                            (a!16 (and (and true
                                                            (and (distinct ES_X_plus
                                                                           emptyset)
                                                                 (distinct ES_X_minus
                                                                           emptyset)))
                                                       (not a!15)))
                                            (a!20 (and (and true
                                                            (and (= ES_X_plus
                                                                    emptyset)
                                                                 (= ES_X_minus
                                                                    emptyset)))
                                                       (not a!19))))
                                        (and (not a!6)
                                             (not a!12)
                                             (not a!16)
                                             (not a!20)))))))))
                         (a!93 (not (and (= (setminus E_S1_minus E_S2_minus)
                                            emptyset)
                                         (= (setminus E_S1_plus emptyset)
                                            emptyset))))
                         (a!94 (not (forall ((ES_X_plus SetInt)
                                             (ES_X_minus SetInt))
                                      (let ((a!1 (and (= emptyset emptyset)
                                                      (>= (min ES_X_plus)
                                                          (+ (max emptyset) 1))))
                                            (a!2 (or false
                                                     (and (>= (min ES_X_plus) 0)
                                                          (>= (min E_S2_minus)
                                                              1))
                                                     (and (>= (min ES_X_plus) 1)
                                                          (>= (min E_S2_minus)
                                                              0))))
                                            (a!3 (and (= emptyset emptyset)
                                                      (>= (min E_S2_minus)
                                                          (+ (max emptyset) 1))))
                                            (a!7 (and (= ES_X_minus emptyset)
                                                      (>= (min emptyset)
                                                          (+ (max emptyset) 1))))
                                            (a!8 (or false
                                                     (and (>= (min emptyset) 0)
                                                          (>= (min E_S2_minus)
                                                              1))
                                                     (and (>= (min emptyset) 1)
                                                          (>= (min E_S2_minus)
                                                              0))))
                                            (a!9 (and (= emptyset emptyset)
                                                      (>= (min E_S2_minus)
                                                          (+ (max ES_X_minus) 1))))
                                            (a!13 (and (= ES_X_minus emptyset)
                                                       (>= (min ES_X_plus)
                                                           (+ (max emptyset) 1))))
                                            (a!17 (and (= emptyset emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max emptyset) 1)))))
                                      (let ((a!4 (or a!1
                                                     (and (and (= emptyset
                                                                  emptyset)
                                                               (= emptyset
                                                                  emptyset))
                                                          a!2)
                                                     a!3))
                                            (a!10 (or a!7
                                                      (and (and (= ES_X_minus
                                                                   emptyset)
                                                                (= emptyset
                                                                   emptyset))
                                                           a!8)
                                                      a!9))
                                            (a!14 (or a!13
                                                      (and (and (= ES_X_minus
                                                                   emptyset)
                                                                (= emptyset
                                                                   emptyset))
                                                           a!2)
                                                      a!9))
                                            (a!18 (or a!17
                                                      (and (and (= emptyset
                                                                   emptyset)
                                                                (= emptyset
                                                                   emptyset))
                                                           a!8)
                                                      a!3)))
                                      (let ((a!5 (not (and a!4
                                                           (= emptyset
                                                              (setminus E_S1_minus
                                                                        E_S2_minus))
                                                           (= ES_X_plus
                                                              (setminus E_S1_plus
                                                                        emptyset)))))
                                            (a!11 (not (and a!10
                                                            (= ES_X_minus
                                                               (setminus E_S1_minus
                                                                         E_S2_minus))
                                                            (= emptyset
                                                               (setminus E_S1_plus
                                                                         emptyset)))))
                                            (a!15 (not (and a!14
                                                            (= ES_X_minus
                                                               (setminus E_S1_minus
                                                                         E_S2_minus))
                                                            (= ES_X_plus
                                                               (setminus E_S1_plus
                                                                         emptyset)))))
                                            (a!19 (not (and a!18
                                                            (= emptyset
                                                               (setminus E_S1_minus
                                                                         E_S2_minus))
                                                            (= emptyset
                                                               (setminus E_S1_plus
                                                                         emptyset))))))
                                      (let ((a!6 (and (and true
                                                           (and (distinct ES_X_plus
                                                                          emptyset)
                                                                (= ES_X_minus
                                                                   emptyset)))
                                                      (not a!5)))
                                            (a!12 (and (and true
                                                            (and (= ES_X_plus
                                                                    emptyset)
                                                                 (distinct ES_X_minus
                                                                           emptyset)))
                                                       (not a!11)))
                                            (a!16 (and (and true
                                                            (and (distinct ES_X_plus
                                                                           emptyset)
                                                                 (distinct ES_X_minus
                                                                           emptyset)))
                                                       (not a!15)))
                                            (a!20 (and (and true
                                                            (and (= ES_X_plus
                                                                    emptyset)
                                                                 (= ES_X_minus
                                                                    emptyset)))
                                                       (not a!19))))
                                        (and (not a!6)
                                             (not a!12)
                                             (not a!16)
                                             (not a!20)))))))))
                         (a!97 (not (and (= (setminus emptyset E_S2_minus)
                                            emptyset)
                                         (= (setminus emptyset emptyset)
                                            emptyset))))
                         (a!98 (not (forall ((ES_X_plus SetInt)
                                             (ES_X_minus SetInt))
                                      (let ((a!1 (and (= emptyset emptyset)
                                                      (>= (min ES_X_plus)
                                                          (+ (max emptyset) 1))))
                                            (a!2 (or false
                                                     (and (>= (min ES_X_plus) 0)
                                                          (>= (min E_S2_minus)
                                                              1))
                                                     (and (>= (min ES_X_plus) 1)
                                                          (>= (min E_S2_minus)
                                                              0))))
                                            (a!3 (and (= emptyset emptyset)
                                                      (>= (min E_S2_minus)
                                                          (+ (max emptyset) 1))))
                                            (a!7 (and (= ES_X_minus emptyset)
                                                      (>= (min emptyset)
                                                          (+ (max emptyset) 1))))
                                            (a!8 (or false
                                                     (and (>= (min emptyset) 0)
                                                          (>= (min E_S2_minus)
                                                              1))
                                                     (and (>= (min emptyset) 1)
                                                          (>= (min E_S2_minus)
                                                              0))))
                                            (a!9 (and (= emptyset emptyset)
                                                      (>= (min E_S2_minus)
                                                          (+ (max ES_X_minus) 1))))
                                            (a!13 (and (= ES_X_minus emptyset)
                                                       (>= (min ES_X_plus)
                                                           (+ (max emptyset) 1))))
                                            (a!17 (and (= emptyset emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max emptyset) 1)))))
                                      (let ((a!4 (or a!1
                                                     (and (and (= emptyset
                                                                  emptyset)
                                                               (= emptyset
                                                                  emptyset))
                                                          a!2)
                                                     a!3))
                                            (a!10 (or a!7
                                                      (and (and (= ES_X_minus
                                                                   emptyset)
                                                                (= emptyset
                                                                   emptyset))
                                                           a!8)
                                                      a!9))
                                            (a!14 (or a!13
                                                      (and (and (= ES_X_minus
                                                                   emptyset)
                                                                (= emptyset
                                                                   emptyset))
                                                           a!2)
                                                      a!9))
                                            (a!18 (or a!17
                                                      (and (and (= emptyset
                                                                   emptyset)
                                                                (= emptyset
                                                                   emptyset))
                                                           a!8)
                                                      a!3)))
                                      (let ((a!5 (not (and a!4
                                                           (= emptyset
                                                              (setminus emptyset
                                                                        E_S2_minus))
                                                           (= ES_X_plus
                                                              (setminus emptyset
                                                                        emptyset)))))
                                            (a!11 (not (and a!10
                                                            (= ES_X_minus
                                                               (setminus emptyset
                                                                         E_S2_minus))
                                                            (= emptyset
                                                               (setminus emptyset
                                                                         emptyset)))))
                                            (a!15 (not (and a!14
                                                            (= ES_X_minus
                                                               (setminus emptyset
                                                                         E_S2_minus))
                                                            (= ES_X_plus
                                                               (setminus emptyset
                                                                         emptyset)))))
                                            (a!19 (not (and a!18
                                                            (= emptyset
                                                               (setminus emptyset
                                                                         E_S2_minus))
                                                            (= emptyset
                                                               (setminus emptyset
                                                                         emptyset))))))
                                      (let ((a!6 (and (and true
                                                           (and (distinct ES_X_plus
                                                                          emptyset)
                                                                (= ES_X_minus
                                                                   emptyset)))
                                                      (not a!5)))
                                            (a!12 (and (and true
                                                            (and (= ES_X_plus
                                                                    emptyset)
                                                                 (distinct ES_X_minus
                                                                           emptyset)))
                                                       (not a!11)))
                                            (a!16 (and (and true
                                                            (and (distinct ES_X_plus
                                                                           emptyset)
                                                                 (distinct ES_X_minus
                                                                           emptyset)))
                                                       (not a!15)))
                                            (a!20 (and (and true
                                                            (and (= ES_X_plus
                                                                    emptyset)
                                                                 (= ES_X_minus
                                                                    emptyset)))
                                                       (not a!19))))
                                        (and (not a!6)
                                             (not a!12)
                                             (not a!16)
                                             (not a!20)))))))))
                         (a!101 (not (and (= (setminus emptyset E_S2_minus)
                                             emptyset)
                                          (= (setminus E_S1_plus E_S2_plus)
                                             emptyset))))
                         (a!102 (not (forall ((ES_X_plus SetInt)
                                              (ES_X_minus SetInt))
                                       (let ((a!1 (and (= emptyset emptyset)
                                                       (>= (min ES_X_plus)
                                                           (+ (max E_S2_plus) 1))))
                                             (a!2 (or false
                                                      (and (>= (min ES_X_plus)
                                                               0)
                                                           (>= (min E_S2_minus)
                                                               1))
                                                      (and (>= (min ES_X_plus)
                                                               1)
                                                           (>= (min E_S2_minus)
                                                               0))))
                                             (a!3 (and (= E_S2_plus emptyset)
                                                       (>= (min E_S2_minus)
                                                           (+ (max emptyset) 1))))
                                             (a!7 (and (= ES_X_minus emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max E_S2_plus) 1))))
                                             (a!8 (or false
                                                      (and (>= (min emptyset) 0)
                                                           (>= (min E_S2_minus)
                                                               1))
                                                      (and (>= (min emptyset) 1)
                                                           (>= (min E_S2_minus)
                                                               0))))
                                             (a!9 (and (= E_S2_plus emptyset)
                                                       (>= (min E_S2_minus)
                                                           (+ (max ES_X_minus)
                                                              1))))
                                             (a!13 (and (= ES_X_minus emptyset)
                                                        (>= (min ES_X_plus)
                                                            (+ (max E_S2_plus)
                                                               1))))
                                             (a!17 (and (= emptyset emptyset)
                                                        (>= (min emptyset)
                                                            (+ (max E_S2_plus)
                                                               1)))))
                                       (let ((a!4 (or a!1
                                                      (and (and (= emptyset
                                                                   emptyset)
                                                                (= E_S2_plus
                                                                   emptyset))
                                                           a!2)
                                                      a!3))
                                             (a!10 (or a!7
                                                       (and (and (= ES_X_minus
                                                                    emptyset)
                                                                 (= E_S2_plus
                                                                    emptyset))
                                                            a!8)
                                                       a!9))
                                             (a!14 (or a!13
                                                       (and (and (= ES_X_minus
                                                                    emptyset)
                                                                 (= E_S2_plus
                                                                    emptyset))
                                                            a!2)
                                                       a!9))
                                             (a!18 (or a!17
                                                       (and (and (= emptyset
                                                                    emptyset)
                                                                 (= E_S2_plus
                                                                    emptyset))
                                                            a!8)
                                                       a!3)))
                                       (let ((a!5 (not (and a!4
                                                            (= emptyset
                                                               (setminus emptyset
                                                                         E_S2_minus))
                                                            (= ES_X_plus
                                                               (setminus E_S1_plus
                                                                         E_S2_plus)))))
                                             (a!11 (not (and a!10
                                                             (= ES_X_minus
                                                                (setminus emptyset
                                                                          E_S2_minus))
                                                             (= emptyset
                                                                (setminus E_S1_plus
                                                                          E_S2_plus)))))
                                             (a!15 (not (and a!14
                                                             (= ES_X_minus
                                                                (setminus emptyset
                                                                          E_S2_minus))
                                                             (= ES_X_plus
                                                                (setminus E_S1_plus
                                                                          E_S2_plus)))))
                                             (a!19 (not (and a!18
                                                             (= emptyset
                                                                (setminus emptyset
                                                                          E_S2_minus))
                                                             (= emptyset
                                                                (setminus E_S1_plus
                                                                          E_S2_plus))))))
                                       (let ((a!6 (and (and true
                                                            (and (distinct ES_X_plus
                                                                           emptyset)
                                                                 (= ES_X_minus
                                                                    emptyset)))
                                                       (not a!5)))
                                             (a!12 (and (and true
                                                             (and (= ES_X_plus
                                                                     emptyset)
                                                                  (distinct ES_X_minus
                                                                            emptyset)))
                                                        (not a!11)))
                                             (a!16 (and (and true
                                                             (and (distinct ES_X_plus
                                                                            emptyset)
                                                                  (distinct ES_X_minus
                                                                            emptyset)))
                                                        (not a!15)))
                                             (a!20 (and (and true
                                                             (and (= ES_X_plus
                                                                     emptyset)
                                                                  (= ES_X_minus
                                                                     emptyset)))
                                                        (not a!19))))
                                         (and (not a!6)
                                              (not a!12)
                                              (not a!16)
                                              (not a!20)))))))))
                         (a!103 (and (and (= E_S2_plus emptyset)
                                          (= S2_plus emptyset))
                                     (<= (min S2_minus) (+ (min E_S2_minus) 1))))
                         (a!105 (and (and (= E_S2_plus emptyset)
                                          (= S2_plus emptyset))
                                     (>= (min S2_minus) (+ (min E_S2_minus) 1))))
                         (a!106 (and (= E_S2_minus emptyset)
                                     (>= (max E_S2_plus) (+ (min E_S2_plus) 1))))
                         (a!107 (and (= E_S2_plus emptyset)
                                     (>= (max E_S2_minus)
                                         (+ (min E_S2_minus) 1))))
                         (a!111 (not (and (= (setminus E_S1_minus E_S2_minus)
                                             emptyset)
                                          (= (setminus emptyset E_S2_plus)
                                             emptyset))))
                         (a!112 (not (forall ((ES_X_plus SetInt)
                                              (ES_X_minus SetInt))
                                       (let ((a!1 (and (= emptyset emptyset)
                                                       (>= (min ES_X_plus)
                                                           (+ (max E_S2_plus) 1))))
                                             (a!2 (or false
                                                      (and (>= (min ES_X_plus)
                                                               0)
                                                           (>= (min E_S2_minus)
                                                               1))
                                                      (and (>= (min ES_X_plus)
                                                               1)
                                                           (>= (min E_S2_minus)
                                                               0))))
                                             (a!3 (and (= E_S2_plus emptyset)
                                                       (>= (min E_S2_minus)
                                                           (+ (max emptyset) 1))))
                                             (a!7 (and (= ES_X_minus emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max E_S2_plus) 1))))
                                             (a!8 (or false
                                                      (and (>= (min emptyset) 0)
                                                           (>= (min E_S2_minus)
                                                               1))
                                                      (and (>= (min emptyset) 1)
                                                           (>= (min E_S2_minus)
                                                               0))))
                                             (a!9 (and (= E_S2_plus emptyset)
                                                       (>= (min E_S2_minus)
                                                           (+ (max ES_X_minus)
                                                              1))))
                                             (a!13 (and (= ES_X_minus emptyset)
                                                        (>= (min ES_X_plus)
                                                            (+ (max E_S2_plus)
                                                               1))))
                                             (a!17 (and (= emptyset emptyset)
                                                        (>= (min emptyset)
                                                            (+ (max E_S2_plus)
                                                               1)))))
                                       (let ((a!4 (or a!1
                                                      (and (and (= emptyset
                                                                   emptyset)
                                                                (= E_S2_plus
                                                                   emptyset))
                                                           a!2)
                                                      a!3))
                                             (a!10 (or a!7
                                                       (and (and (= ES_X_minus
                                                                    emptyset)
                                                                 (= E_S2_plus
                                                                    emptyset))
                                                            a!8)
                                                       a!9))
                                             (a!14 (or a!13
                                                       (and (and (= ES_X_minus
                                                                    emptyset)
                                                                 (= E_S2_plus
                                                                    emptyset))
                                                            a!2)
                                                       a!9))
                                             (a!18 (or a!17
                                                       (and (and (= emptyset
                                                                    emptyset)
                                                                 (= E_S2_plus
                                                                    emptyset))
                                                            a!8)
                                                       a!3)))
                                       (let ((a!5 (not (and a!4
                                                            (= emptyset
                                                               (setminus E_S1_minus
                                                                         E_S2_minus))
                                                            (= ES_X_plus
                                                               (setminus emptyset
                                                                         E_S2_plus)))))
                                             (a!11 (not (and a!10
                                                             (= ES_X_minus
                                                                (setminus E_S1_minus
                                                                          E_S2_minus))
                                                             (= emptyset
                                                                (setminus emptyset
                                                                          E_S2_plus)))))
                                             (a!15 (not (and a!14
                                                             (= ES_X_minus
                                                                (setminus E_S1_minus
                                                                          E_S2_minus))
                                                             (= ES_X_plus
                                                                (setminus emptyset
                                                                          E_S2_plus)))))
                                             (a!19 (not (and a!18
                                                             (= emptyset
                                                                (setminus E_S1_minus
                                                                          E_S2_minus))
                                                             (= emptyset
                                                                (setminus emptyset
                                                                          E_S2_plus))))))
                                       (let ((a!6 (and (and true
                                                            (and (distinct ES_X_plus
                                                                           emptyset)
                                                                 (= ES_X_minus
                                                                    emptyset)))
                                                       (not a!5)))
                                             (a!12 (and (and true
                                                             (and (= ES_X_plus
                                                                     emptyset)
                                                                  (distinct ES_X_minus
                                                                            emptyset)))
                                                        (not a!11)))
                                             (a!16 (and (and true
                                                             (and (distinct ES_X_plus
                                                                            emptyset)
                                                                  (distinct ES_X_minus
                                                                            emptyset)))
                                                        (not a!15)))
                                             (a!20 (and (and true
                                                             (and (= ES_X_plus
                                                                     emptyset)
                                                                  (= ES_X_minus
                                                                     emptyset)))
                                                        (not a!19))))
                                         (and (not a!6)
                                              (not a!12)
                                              (not a!16)
                                              (not a!20)))))))))
                         (a!115 (not (and (= (setminus E_S1_minus E_S2_minus)
                                             emptyset)
                                          (= (setminus E_S1_plus E_S2_plus)
                                             emptyset))))
                         (a!116 (not (forall ((ES_X_plus SetInt)
                                              (ES_X_minus SetInt))
                                       (let ((a!1 (and (= emptyset emptyset)
                                                       (>= (min ES_X_plus)
                                                           (+ (max E_S2_plus) 1))))
                                             (a!2 (or false
                                                      (and (>= (min ES_X_plus)
                                                               0)
                                                           (>= (min E_S2_minus)
                                                               1))
                                                      (and (>= (min ES_X_plus)
                                                               1)
                                                           (>= (min E_S2_minus)
                                                               0))))
                                             (a!3 (and (= E_S2_plus emptyset)
                                                       (>= (min E_S2_minus)
                                                           (+ (max emptyset) 1))))
                                             (a!7 (and (= ES_X_minus emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max E_S2_plus) 1))))
                                             (a!8 (or false
                                                      (and (>= (min emptyset) 0)
                                                           (>= (min E_S2_minus)
                                                               1))
                                                      (and (>= (min emptyset) 1)
                                                           (>= (min E_S2_minus)
                                                               0))))
                                             (a!9 (and (= E_S2_plus emptyset)
                                                       (>= (min E_S2_minus)
                                                           (+ (max ES_X_minus)
                                                              1))))
                                             (a!13 (and (= ES_X_minus emptyset)
                                                        (>= (min ES_X_plus)
                                                            (+ (max E_S2_plus)
                                                               1))))
                                             (a!17 (and (= emptyset emptyset)
                                                        (>= (min emptyset)
                                                            (+ (max E_S2_plus)
                                                               1)))))
                                       (let ((a!4 (or a!1
                                                      (and (and (= emptyset
                                                                   emptyset)
                                                                (= E_S2_plus
                                                                   emptyset))
                                                           a!2)
                                                      a!3))
                                             (a!10 (or a!7
                                                       (and (and (= ES_X_minus
                                                                    emptyset)
                                                                 (= E_S2_plus
                                                                    emptyset))
                                                            a!8)
                                                       a!9))
                                             (a!14 (or a!13
                                                       (and (and (= ES_X_minus
                                                                    emptyset)
                                                                 (= E_S2_plus
                                                                    emptyset))
                                                            a!2)
                                                       a!9))
                                             (a!18 (or a!17
                                                       (and (and (= emptyset
                                                                    emptyset)
                                                                 (= E_S2_plus
                                                                    emptyset))
                                                            a!8)
                                                       a!3)))
                                       (let ((a!5 (not (and a!4
                                                            (= emptyset
                                                               (setminus E_S1_minus
                                                                         E_S2_minus))
                                                            (= ES_X_plus
                                                               (setminus E_S1_plus
                                                                         E_S2_plus)))))
                                             (a!11 (not (and a!10
                                                             (= ES_X_minus
                                                                (setminus E_S1_minus
                                                                          E_S2_minus))
                                                             (= emptyset
                                                                (setminus E_S1_plus
                                                                          E_S2_plus)))))
                                             (a!15 (not (and a!14
                                                             (= ES_X_minus
                                                                (setminus E_S1_minus
                                                                          E_S2_minus))
                                                             (= ES_X_plus
                                                                (setminus E_S1_plus
                                                                          E_S2_plus)))))
                                             (a!19 (not (and a!18
                                                             (= emptyset
                                                                (setminus E_S1_minus
                                                                          E_S2_minus))
                                                             (= emptyset
                                                                (setminus E_S1_plus
                                                                          E_S2_plus))))))
                                       (let ((a!6 (and (and true
                                                            (and (distinct ES_X_plus
                                                                           emptyset)
                                                                 (= ES_X_minus
                                                                    emptyset)))
                                                       (not a!5)))
                                             (a!12 (and (and true
                                                             (and (= ES_X_plus
                                                                     emptyset)
                                                                  (distinct ES_X_minus
                                                                            emptyset)))
                                                        (not a!11)))
                                             (a!16 (and (and true
                                                             (and (distinct ES_X_plus
                                                                            emptyset)
                                                                  (distinct ES_X_minus
                                                                            emptyset)))
                                                        (not a!15)))
                                             (a!20 (and (and true
                                                             (and (= ES_X_plus
                                                                     emptyset)
                                                                  (= ES_X_minus
                                                                     emptyset)))
                                                        (not a!19))))
                                         (and (not a!6)
                                              (not a!12)
                                              (not a!16)
                                              (not a!20)))))))))
                         (a!119 (not (and (= (setminus emptyset E_S2_minus)
                                             emptyset)
                                          (= (setminus emptyset E_S2_plus)
                                             emptyset))))
                         (a!120 (not (forall ((ES_X_plus SetInt)
                                              (ES_X_minus SetInt))
                                       (let ((a!1 (and (= emptyset emptyset)
                                                       (>= (min ES_X_plus)
                                                           (+ (max E_S2_plus) 1))))
                                             (a!2 (or false
                                                      (and (>= (min ES_X_plus)
                                                               0)
                                                           (>= (min E_S2_minus)
                                                               1))
                                                      (and (>= (min ES_X_plus)
                                                               1)
                                                           (>= (min E_S2_minus)
                                                               0))))
                                             (a!3 (and (= E_S2_plus emptyset)
                                                       (>= (min E_S2_minus)
                                                           (+ (max emptyset) 1))))
                                             (a!7 (and (= ES_X_minus emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max E_S2_plus) 1))))
                                             (a!8 (or false
                                                      (and (>= (min emptyset) 0)
                                                           (>= (min E_S2_minus)
                                                               1))
                                                      (and (>= (min emptyset) 1)
                                                           (>= (min E_S2_minus)
                                                               0))))
                                             (a!9 (and (= E_S2_plus emptyset)
                                                       (>= (min E_S2_minus)
                                                           (+ (max ES_X_minus)
                                                              1))))
                                             (a!13 (and (= ES_X_minus emptyset)
                                                        (>= (min ES_X_plus)
                                                            (+ (max E_S2_plus)
                                                               1))))
                                             (a!17 (and (= emptyset emptyset)
                                                        (>= (min emptyset)
                                                            (+ (max E_S2_plus)
                                                               1)))))
                                       (let ((a!4 (or a!1
                                                      (and (and (= emptyset
                                                                   emptyset)
                                                                (= E_S2_plus
                                                                   emptyset))
                                                           a!2)
                                                      a!3))
                                             (a!10 (or a!7
                                                       (and (and (= ES_X_minus
                                                                    emptyset)
                                                                 (= E_S2_plus
                                                                    emptyset))
                                                            a!8)
                                                       a!9))
                                             (a!14 (or a!13
                                                       (and (and (= ES_X_minus
                                                                    emptyset)
                                                                 (= E_S2_plus
                                                                    emptyset))
                                                            a!2)
                                                       a!9))
                                             (a!18 (or a!17
                                                       (and (and (= emptyset
                                                                    emptyset)
                                                                 (= E_S2_plus
                                                                    emptyset))
                                                            a!8)
                                                       a!3)))
                                       (let ((a!5 (not (and a!4
                                                            (= emptyset
                                                               (setminus emptyset
                                                                         E_S2_minus))
                                                            (= ES_X_plus
                                                               (setminus emptyset
                                                                         E_S2_plus)))))
                                             (a!11 (not (and a!10
                                                             (= ES_X_minus
                                                                (setminus emptyset
                                                                          E_S2_minus))
                                                             (= emptyset
                                                                (setminus emptyset
                                                                          E_S2_plus)))))
                                             (a!15 (not (and a!14
                                                             (= ES_X_minus
                                                                (setminus emptyset
                                                                          E_S2_minus))
                                                             (= ES_X_plus
                                                                (setminus emptyset
                                                                          E_S2_plus)))))
                                             (a!19 (not (and a!18
                                                             (= emptyset
                                                                (setminus emptyset
                                                                          E_S2_minus))
                                                             (= emptyset
                                                                (setminus emptyset
                                                                          E_S2_plus))))))
                                       (let ((a!6 (and (and true
                                                            (and (distinct ES_X_plus
                                                                           emptyset)
                                                                 (= ES_X_minus
                                                                    emptyset)))
                                                       (not a!5)))
                                             (a!12 (and (and true
                                                             (and (= ES_X_plus
                                                                     emptyset)
                                                                  (distinct ES_X_minus
                                                                            emptyset)))
                                                        (not a!11)))
                                             (a!16 (and (and true
                                                             (and (distinct ES_X_plus
                                                                            emptyset)
                                                                  (distinct ES_X_minus
                                                                            emptyset)))
                                                        (not a!15)))
                                             (a!20 (and (and true
                                                             (and (= ES_X_plus
                                                                     emptyset)
                                                                  (= ES_X_minus
                                                                     emptyset)))
                                                        (not a!19))))
                                         (and (not a!6)
                                              (not a!12)
                                              (not a!16)
                                              (not a!20)))))))))
                         (a!123 (not (and (= (setminus emptyset emptyset)
                                             emptyset)
                                          (= (setminus E_S1_plus emptyset)
                                             emptyset))))
                         (a!124 (not (forall ((ES_X_plus SetInt)
                                              (ES_X_minus SetInt))
                                       (let ((a!1 (and (= emptyset emptyset)
                                                       (>= (min ES_X_plus)
                                                           (+ (max emptyset) 1))))
                                             (a!2 (or false
                                                      (and (>= (min ES_X_plus)
                                                               0)
                                                           (>= (min emptyset) 1))
                                                      (and (>= (min ES_X_plus)
                                                               1)
                                                           (>= (min emptyset) 0))))
                                             (a!3 (and (= emptyset emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max emptyset) 1))))
                                             (a!7 (and (= ES_X_minus emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max emptyset) 1))))
                                             (a!8 (or false
                                                      (and (>= (min emptyset) 0)
                                                           (>= (min emptyset) 1))
                                                      (and (>= (min emptyset) 1)
                                                           (>= (min emptyset) 0))))
                                             (a!9 (and (= emptyset emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max ES_X_minus)
                                                              1))))
                                             (a!13 (and (= ES_X_minus emptyset)
                                                        (>= (min ES_X_plus)
                                                            (+ (max emptyset) 1)))))
                                       (let ((a!4 (or a!1
                                                      (and (and (= emptyset
                                                                   emptyset)
                                                                (= emptyset
                                                                   emptyset))
                                                           a!2)
                                                      a!3))
                                             (a!10 (or a!7
                                                       (and (and (= ES_X_minus
                                                                    emptyset)
                                                                 (= emptyset
                                                                    emptyset))
                                                            a!8)
                                                       a!9))
                                             (a!14 (or a!13
                                                       (and (and (= ES_X_minus
                                                                    emptyset)
                                                                 (= emptyset
                                                                    emptyset))
                                                            a!2)
                                                       a!9))
                                             (a!17 (or a!3
                                                       (and (and (= emptyset
                                                                    emptyset)
                                                                 (= emptyset
                                                                    emptyset))
                                                            a!8)
                                                       a!3)))
                                       (let ((a!5 (not (and a!4
                                                            (= emptyset
                                                               (setminus emptyset
                                                                         emptyset))
                                                            (= ES_X_plus
                                                               (setminus E_S1_plus
                                                                         emptyset)))))
                                             (a!11 (not (and a!10
                                                             (= ES_X_minus
                                                                (setminus emptyset
                                                                          emptyset))
                                                             (= emptyset
                                                                (setminus E_S1_plus
                                                                          emptyset)))))
                                             (a!15 (not (and a!14
                                                             (= ES_X_minus
                                                                (setminus emptyset
                                                                          emptyset))
                                                             (= ES_X_plus
                                                                (setminus E_S1_plus
                                                                          emptyset)))))
                                             (a!18 (not (and a!17
                                                             (= emptyset
                                                                (setminus emptyset
                                                                          emptyset))
                                                             (= emptyset
                                                                (setminus E_S1_plus
                                                                          emptyset))))))
                                       (let ((a!6 (and (and true
                                                            (and (distinct ES_X_plus
                                                                           emptyset)
                                                                 (= ES_X_minus
                                                                    emptyset)))
                                                       (not a!5)))
                                             (a!12 (and (and true
                                                             (and (= ES_X_plus
                                                                     emptyset)
                                                                  (distinct ES_X_minus
                                                                            emptyset)))
                                                        (not a!11)))
                                             (a!16 (and (and true
                                                             (and (distinct ES_X_plus
                                                                            emptyset)
                                                                  (distinct ES_X_minus
                                                                            emptyset)))
                                                        (not a!15)))
                                             (a!19 (and (and true
                                                             (and (= ES_X_plus
                                                                     emptyset)
                                                                  (= ES_X_minus
                                                                     emptyset)))
                                                        (not a!18))))
                                         (and (not a!6)
                                              (not a!12)
                                              (not a!16)
                                              (not a!19)))))))))
                         (a!125 (and (and (= emptyset emptyset)
                                          (= S2_plus emptyset))
                                     (<= (min S2_minus) (+ (min emptyset) 1))))
                         (a!126 (and (and (= emptyset emptyset)
                                          (= S2_plus emptyset))
                                     (>= (min S2_minus) (+ (min emptyset) 1))))
                         (a!128 (and (= emptyset emptyset)
                                     (>= (max emptyset) (+ (min emptyset) 1))))
                         (a!130 (forall ((y_plus Int)
                                         (y_minus Int)
                                         (x_plus Int)
                                         (x_minus Int))
                                  (let ((a!1 (not (and true
                                                       (<= y_plus (+ x_plus 1))
                                                       (>= y_plus (+ x_plus 1)))))
                                        (a!4 (and (and true (= y_minus 0))
                                                  (and (= x_plus 0)
                                                       (> x_minus 0))))
                                        (a!5 (or false
                                                 (and (>= y_plus 0)
                                                      (>= x_minus 1))
                                                 (and (>= y_plus 1)
                                                      (>= x_minus 0))))
                                        (a!9 (and (and true
                                                       (= y_plus 0)
                                                       (> y_minus 0))
                                                  (= x_minus 0)))
                                        (a!10 (and (and false false)
                                                   false
                                                   (forall ((z_plus Int)
                                                            (z_minus Int))
                                                     (let ((a!1 (and false
                                                                     (and (>= z_plus
                                                                              (+ x_plus
                                                                                 1))
                                                                          false)))
                                                           (a!3 (and false
                                                                     (and false
                                                                          (>= z_minus
                                                                              (+ y_minus
                                                                                 1))))))
                                                     (let ((a!2 (not (and (and true
                                                                               (= z_minus
                                                                                  0))
                                                                          (not (not a!1)))))
                                                           (a!4 (and (and true
                                                                          (and (= z_plus
                                                                                  0)
                                                                               (> z_minus
                                                                                  0)))
                                                                     (not (not a!3)))))
                                                       (and a!2 (not a!4)))))
                                                   (not (and true true false))))
                                        (a!12 (and (and true
                                                        (= y_plus 0)
                                                        (> y_minus 0))
                                                   (and (= x_plus 0)
                                                        (> x_minus 0))))
                                        (a!13 (not (and true
                                                        (<= x_minus
                                                            (+ y_minus 1))
                                                        (>= x_minus
                                                            (+ y_minus 1))))))
                                  (let ((a!2 (and (and false false)
                                                  (>= y_plus (+ x_plus 1))
                                                  (forall ((z_plus Int)
                                                           (z_minus Int))
                                                    (let ((a!1 (and (>= z_plus
                                                                        (+ x_plus
                                                                           1))
                                                                    (>= y_plus
                                                                        (+ z_plus
                                                                           1))))
                                                          (a!3 (or false
                                                                   (and (>= y_plus
                                                                            0)
                                                                        (>= z_minus
                                                                            1))
                                                                   (and (>= y_plus
                                                                            1)
                                                                        (>= z_minus
                                                                            0)))))
                                                    (let ((a!2 (and (and true
                                                                         (= z_minus
                                                                            0))
                                                                    (not (not (and false
                                                                                   a!1)))))
                                                          (a!4 (not (not (and false
                                                                              (and false
                                                                                   a!3))))))
                                                    (let ((a!5 (and (and true
                                                                         (and (= z_plus
                                                                                 0)
                                                                              (> z_minus
                                                                                 0)))
                                                                    a!4)))
                                                      (and (not a!2) (not a!5))))))
                                                  a!1))
                                        (a!6 (and true
                                                  (or false
                                                      (and (<= y_plus 0)
                                                           (<= x_minus 1))
                                                      (and (<= y_plus 1)
                                                           (<= x_minus 0)))
                                                  a!5))
                                        (a!11 (not (and a!9 (not (not a!10)))))
                                        (a!14 (and (and false false)
                                                   (>= x_minus (+ y_minus 1))
                                                   (forall ((z_plus Int)
                                                            (z_minus Int))
                                                     (let ((a!1 (or false
                                                                    (and (>= z_plus
                                                                             0)
                                                                         (>= x_minus
                                                                             1))
                                                                    (and (>= z_plus
                                                                             1)
                                                                         (>= x_minus
                                                                             0))))
                                                           (a!4 (and (>= x_minus
                                                                         (+ z_minus
                                                                            1))
                                                                     (>= z_minus
                                                                         (+ y_minus
                                                                            1)))))
                                                     (let ((a!2 (not (not (and false
                                                                               (and a!1
                                                                                    false)))))
                                                           (a!5 (and (and true
                                                                          (and (= z_plus
                                                                                  0)
                                                                               (> z_minus
                                                                                  0)))
                                                                     (not (not (and false
                                                                                    a!4))))))
                                                     (let ((a!3 (not (and (and true
                                                                               (= z_minus
                                                                                  0))
                                                                          a!2))))
                                                       (and a!3 (not a!5))))))
                                                   a!13)))
                                  (let ((a!3 (and (and (and true (= y_minus 0))
                                                       (= x_minus 0))
                                                  (not (not a!2))))
                                        (a!7 (and (and false false)
                                                  a!5
                                                  (forall ((z_plus Int)
                                                           (z_minus Int))
                                                    (let ((a!1 (or false
                                                                   (and (>= z_plus
                                                                            0)
                                                                        (>= x_minus
                                                                            1))
                                                                   (and (>= z_plus
                                                                            1)
                                                                        (>= x_minus
                                                                            0))))
                                                          (a!4 (or false
                                                                   (and (>= y_plus
                                                                            0)
                                                                        (>= z_minus
                                                                            1))
                                                                   (and (>= y_plus
                                                                            1)
                                                                        (>= z_minus
                                                                            0)))))
                                                    (let ((a!2 (and false
                                                                    (and a!1
                                                                         (>= y_plus
                                                                             (+ z_plus
                                                                                1)))))
                                                          (a!5 (and false
                                                                    (and (>= x_minus
                                                                             (+ z_minus
                                                                                1))
                                                                         a!4))))
                                                    (let ((a!3 (not (and (and true
                                                                              (= z_minus
                                                                                 0))
                                                                         (not (not a!2)))))
                                                          (a!6 (and (and true
                                                                         (and (= z_plus
                                                                                 0)
                                                                              (> z_minus
                                                                                 0)))
                                                                    (not (not a!5)))))
                                                      (and a!3 (not a!6))))))
                                                  (not a!6)))
                                        (a!15 (not (and a!12 (not (not a!14))))))
                                  (let ((a!8 (not (and a!4 (not (not a!7))))))
                                    (and (not a!3) a!8 a!11 a!15)))))))
                         (a!133 (not (and (= (setminus E_S1_minus emptyset)
                                             emptyset)
                                          (= (setminus emptyset emptyset)
                                             emptyset))))
                         (a!134 (not (forall ((ES_X_plus SetInt)
                                              (ES_X_minus SetInt))
                                       (let ((a!1 (and (= emptyset emptyset)
                                                       (>= (min ES_X_plus)
                                                           (+ (max emptyset) 1))))
                                             (a!2 (or false
                                                      (and (>= (min ES_X_plus)
                                                               0)
                                                           (>= (min emptyset) 1))
                                                      (and (>= (min ES_X_plus)
                                                               1)
                                                           (>= (min emptyset) 0))))
                                             (a!3 (and (= emptyset emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max emptyset) 1))))
                                             (a!7 (and (= ES_X_minus emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max emptyset) 1))))
                                             (a!8 (or false
                                                      (and (>= (min emptyset) 0)
                                                           (>= (min emptyset) 1))
                                                      (and (>= (min emptyset) 1)
                                                           (>= (min emptyset) 0))))
                                             (a!9 (and (= emptyset emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max ES_X_minus)
                                                              1))))
                                             (a!13 (and (= ES_X_minus emptyset)
                                                        (>= (min ES_X_plus)
                                                            (+ (max emptyset) 1)))))
                                       (let ((a!4 (or a!1
                                                      (and (and (= emptyset
                                                                   emptyset)
                                                                (= emptyset
                                                                   emptyset))
                                                           a!2)
                                                      a!3))
                                             (a!10 (or a!7
                                                       (and (and (= ES_X_minus
                                                                    emptyset)
                                                                 (= emptyset
                                                                    emptyset))
                                                            a!8)
                                                       a!9))
                                             (a!14 (or a!13
                                                       (and (and (= ES_X_minus
                                                                    emptyset)
                                                                 (= emptyset
                                                                    emptyset))
                                                            a!2)
                                                       a!9))
                                             (a!17 (or a!3
                                                       (and (and (= emptyset
                                                                    emptyset)
                                                                 (= emptyset
                                                                    emptyset))
                                                            a!8)
                                                       a!3)))
                                       (let ((a!5 (not (and a!4
                                                            (= emptyset
                                                               (setminus E_S1_minus
                                                                         emptyset))
                                                            (= ES_X_plus
                                                               (setminus emptyset
                                                                         emptyset)))))
                                             (a!11 (not (and a!10
                                                             (= ES_X_minus
                                                                (setminus E_S1_minus
                                                                          emptyset))
                                                             (= emptyset
                                                                (setminus emptyset
                                                                          emptyset)))))
                                             (a!15 (not (and a!14
                                                             (= ES_X_minus
                                                                (setminus E_S1_minus
                                                                          emptyset))
                                                             (= ES_X_plus
                                                                (setminus emptyset
                                                                          emptyset)))))
                                             (a!18 (not (and a!17
                                                             (= emptyset
                                                                (setminus E_S1_minus
                                                                          emptyset))
                                                             (= emptyset
                                                                (setminus emptyset
                                                                          emptyset))))))
                                       (let ((a!6 (and (and true
                                                            (and (distinct ES_X_plus
                                                                           emptyset)
                                                                 (= ES_X_minus
                                                                    emptyset)))
                                                       (not a!5)))
                                             (a!12 (and (and true
                                                             (and (= ES_X_plus
                                                                     emptyset)
                                                                  (distinct ES_X_minus
                                                                            emptyset)))
                                                        (not a!11)))
                                             (a!16 (and (and true
                                                             (and (distinct ES_X_plus
                                                                            emptyset)
                                                                  (distinct ES_X_minus
                                                                            emptyset)))
                                                        (not a!15)))
                                             (a!19 (and (and true
                                                             (and (= ES_X_plus
                                                                     emptyset)
                                                                  (= ES_X_minus
                                                                     emptyset)))
                                                        (not a!18))))
                                         (and (not a!6)
                                              (not a!12)
                                              (not a!16)
                                              (not a!19)))))))))
                         (a!137 (not (and (= (setminus E_S1_minus emptyset)
                                             emptyset)
                                          (= (setminus E_S1_plus emptyset)
                                             emptyset))))
                         (a!138 (not (forall ((ES_X_plus SetInt)
                                              (ES_X_minus SetInt))
                                       (let ((a!1 (and (= emptyset emptyset)
                                                       (>= (min ES_X_plus)
                                                           (+ (max emptyset) 1))))
                                             (a!2 (or false
                                                      (and (>= (min ES_X_plus)
                                                               0)
                                                           (>= (min emptyset) 1))
                                                      (and (>= (min ES_X_plus)
                                                               1)
                                                           (>= (min emptyset) 0))))
                                             (a!3 (and (= emptyset emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max emptyset) 1))))
                                             (a!7 (and (= ES_X_minus emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max emptyset) 1))))
                                             (a!8 (or false
                                                      (and (>= (min emptyset) 0)
                                                           (>= (min emptyset) 1))
                                                      (and (>= (min emptyset) 1)
                                                           (>= (min emptyset) 0))))
                                             (a!9 (and (= emptyset emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max ES_X_minus)
                                                              1))))
                                             (a!13 (and (= ES_X_minus emptyset)
                                                        (>= (min ES_X_plus)
                                                            (+ (max emptyset) 1)))))
                                       (let ((a!4 (or a!1
                                                      (and (and (= emptyset
                                                                   emptyset)
                                                                (= emptyset
                                                                   emptyset))
                                                           a!2)
                                                      a!3))
                                             (a!10 (or a!7
                                                       (and (and (= ES_X_minus
                                                                    emptyset)
                                                                 (= emptyset
                                                                    emptyset))
                                                            a!8)
                                                       a!9))
                                             (a!14 (or a!13
                                                       (and (and (= ES_X_minus
                                                                    emptyset)
                                                                 (= emptyset
                                                                    emptyset))
                                                            a!2)
                                                       a!9))
                                             (a!17 (or a!3
                                                       (and (and (= emptyset
                                                                    emptyset)
                                                                 (= emptyset
                                                                    emptyset))
                                                            a!8)
                                                       a!3)))
                                       (let ((a!5 (not (and a!4
                                                            (= emptyset
                                                               (setminus E_S1_minus
                                                                         emptyset))
                                                            (= ES_X_plus
                                                               (setminus E_S1_plus
                                                                         emptyset)))))
                                             (a!11 (not (and a!10
                                                             (= ES_X_minus
                                                                (setminus E_S1_minus
                                                                          emptyset))
                                                             (= emptyset
                                                                (setminus E_S1_plus
                                                                          emptyset)))))
                                             (a!15 (not (and a!14
                                                             (= ES_X_minus
                                                                (setminus E_S1_minus
                                                                          emptyset))
                                                             (= ES_X_plus
                                                                (setminus E_S1_plus
                                                                          emptyset)))))
                                             (a!18 (not (and a!17
                                                             (= emptyset
                                                                (setminus E_S1_minus
                                                                          emptyset))
                                                             (= emptyset
                                                                (setminus E_S1_plus
                                                                          emptyset))))))
                                       (let ((a!6 (and (and true
                                                            (and (distinct ES_X_plus
                                                                           emptyset)
                                                                 (= ES_X_minus
                                                                    emptyset)))
                                                       (not a!5)))
                                             (a!12 (and (and true
                                                             (and (= ES_X_plus
                                                                     emptyset)
                                                                  (distinct ES_X_minus
                                                                            emptyset)))
                                                        (not a!11)))
                                             (a!16 (and (and true
                                                             (and (distinct ES_X_plus
                                                                            emptyset)
                                                                  (distinct ES_X_minus
                                                                            emptyset)))
                                                        (not a!15)))
                                             (a!19 (and (and true
                                                             (and (= ES_X_plus
                                                                     emptyset)
                                                                  (= ES_X_minus
                                                                     emptyset)))
                                                        (not a!18))))
                                         (and (not a!6)
                                              (not a!12)
                                              (not a!16)
                                              (not a!19)))))))))
                         (a!141 (not (and (= (setminus emptyset emptyset)
                                             emptyset)
                                          (= (setminus emptyset emptyset)
                                             emptyset))))
                         (a!142 (not (forall ((ES_X_plus SetInt)
                                              (ES_X_minus SetInt))
                                       (let ((a!1 (and (= emptyset emptyset)
                                                       (>= (min ES_X_plus)
                                                           (+ (max emptyset) 1))))
                                             (a!2 (or false
                                                      (and (>= (min ES_X_plus)
                                                               0)
                                                           (>= (min emptyset) 1))
                                                      (and (>= (min ES_X_plus)
                                                               1)
                                                           (>= (min emptyset) 0))))
                                             (a!3 (and (= emptyset emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max emptyset) 1))))
                                             (a!7 (and (= ES_X_minus emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max emptyset) 1))))
                                             (a!8 (or false
                                                      (and (>= (min emptyset) 0)
                                                           (>= (min emptyset) 1))
                                                      (and (>= (min emptyset) 1)
                                                           (>= (min emptyset) 0))))
                                             (a!9 (and (= emptyset emptyset)
                                                       (>= (min emptyset)
                                                           (+ (max ES_X_minus)
                                                              1))))
                                             (a!13 (and (= ES_X_minus emptyset)
                                                        (>= (min ES_X_plus)
                                                            (+ (max emptyset) 1)))))
                                       (let ((a!4 (or a!1
                                                      (and (and (= emptyset
                                                                   emptyset)
                                                                (= emptyset
                                                                   emptyset))
                                                           a!2)
                                                      a!3))
                                             (a!10 (or a!7
                                                       (and (and (= ES_X_minus
                                                                    emptyset)
                                                                 (= emptyset
                                                                    emptyset))
                                                            a!8)
                                                       a!9))
                                             (a!14 (or a!13
                                                       (and (and (= ES_X_minus
                                                                    emptyset)
                                                                 (= emptyset
                                                                    emptyset))
                                                            a!2)
                                                       a!9))
                                             (a!17 (or a!3
                                                       (and (and (= emptyset
                                                                    emptyset)
                                                                 (= emptyset
                                                                    emptyset))
                                                            a!8)
                                                       a!3)))
                                       (let ((a!5 (not (and a!4
                                                            (= emptyset
                                                               (setminus emptyset
                                                                         emptyset))
                                                            (= ES_X_plus
                                                               (setminus emptyset
                                                                         emptyset)))))
                                             (a!11 (not (and a!10
                                                             (= ES_X_minus
                                                                (setminus emptyset
                                                                          emptyset))
                                                             (= emptyset
                                                                (setminus emptyset
                                                                          emptyset)))))
                                             (a!15 (not (and a!14
                                                             (= ES_X_minus
                                                                (setminus emptyset
                                                                          emptyset))
                                                             (= ES_X_plus
                                                                (setminus emptyset
                                                                          emptyset)))))
                                             (a!18 (not (and a!17
                                                             (= emptyset
                                                                (setminus emptyset
                                                                          emptyset))
                                                             (= emptyset
                                                                (setminus emptyset
                                                                          emptyset))))))
                                       (let ((a!6 (and (and true
                                                            (and (distinct ES_X_plus
                                                                           emptyset)
                                                                 (= ES_X_minus
                                                                    emptyset)))
                                                       (not a!5)))
                                             (a!12 (and (and true
                                                             (and (= ES_X_plus
                                                                     emptyset)
                                                                  (distinct ES_X_minus
                                                                            emptyset)))
                                                        (not a!11)))
                                             (a!16 (and (and true
                                                             (and (distinct ES_X_plus
                                                                            emptyset)
                                                                  (distinct ES_X_minus
                                                                            emptyset)))
                                                        (not a!15)))
                                             (a!19 (and (and true
                                                             (and (= ES_X_plus
                                                                     emptyset)
                                                                  (= ES_X_minus
                                                                     emptyset)))
                                                        (not a!18))))
                                         (and (not a!6)
                                              (not a!12)
                                              (not a!16)
                                              (not a!19))))))))))
                   (let ((a!8 (or (<= (max S1_2_plus) (+ (max E_S1_plus) 1))
                                  (and (= E_S1_plus emptyset) a!5)
                                  a!6
                                  a!7))
                         (a!11 (or (>= (max S1_2_plus) (+ (max E_S1_plus) 1))
                                   (and (= E_S1_plus emptyset) a!9)
                                   a!10))
                         (a!13 (or (<= (max E_S2_plus) (+ (max S2_plus) 1))
                                   (and (= S2_plus emptyset) a!12)))
                         (a!16 (or (>= (max E_S2_plus) (+ (max S2_plus) 1))
                                   (and (= S2_plus emptyset) a!15)))
                         (a!21 (or a!19
                                   false
                                   (and (>= (min S1_2_plus) 0)
                                        (>= (max S1_2_minus) 1))
                                   (and (>= (min S1_2_plus) 1)
                                        (>= (max S1_2_minus) 0))
                                   a!20))
                         (a!24 (or a!22
                                   false
                                   (and (>= (min E_S2_plus) 0)
                                        (>= (max emptyset) 1))
                                   (and (>= (min E_S2_plus) 1)
                                        (>= (max emptyset) 0))
                                   a!23))
                         (a!28 (or a!25
                                   (and (and (= S2_minus emptyset)
                                             (= S2_plus emptyset))
                                        a!26)
                                   (and (distinct S2_minus emptyset)
                                        (distinct S2_plus emptyset))
                                   a!27))
                         (a!32 (and true
                                    (or a!29
                                        (and (= emptyset emptyset)
                                             (= E_S1_plus emptyset)
                                             a!30)
                                        (and (distinct emptyset emptyset)
                                             (distinct E_S1_plus emptyset))
                                        a!31)))
                         (a!41 (or (<= (max S1_2_plus) (+ (max emptyset) 1))
                                   (and (= emptyset emptyset) a!38)
                                   a!39
                                   a!40))
                         (a!44 (or (>= (max S1_2_plus) (+ (max emptyset) 1))
                                   (and (= emptyset emptyset) a!42)
                                   a!43))
                         (a!48 (or a!45
                                   (and (and (= E_S1_minus emptyset)
                                             (= emptyset emptyset))
                                        a!46)
                                   (and (distinct E_S1_minus emptyset)
                                        (distinct emptyset emptyset))
                                   a!47))
                         (a!54 (or (<= (max S1_2_plus) (+ (max E_S1_plus) 1))
                                   (and (= E_S1_plus emptyset) a!38)
                                   a!6
                                   a!53))
                         (a!56 (or (>= (max S1_2_plus) (+ (max E_S1_plus) 1))
                                   (and (= E_S1_plus emptyset) a!42)
                                   a!55))
                         (a!60 (and true
                                    (or a!57
                                        (and (= E_S1_minus emptyset)
                                             (= E_S1_plus emptyset)
                                             a!58)
                                        (and (distinct E_S1_minus emptyset)
                                             (distinct E_S1_plus emptyset))
                                        a!59)))
                         (a!66 (or (<= (max S1_2_plus) (+ (max emptyset) 1))
                                   (and (= emptyset emptyset) a!5)
                                   a!39
                                   a!65))
                         (a!68 (or (>= (max S1_2_plus) (+ (max emptyset) 1))
                                   (and (= emptyset emptyset) a!9)
                                   a!67))
                         (a!71 (or a!69
                                   (and (and (= emptyset emptyset)
                                             (= emptyset emptyset))
                                        a!70)
                                   (and (distinct emptyset emptyset)
                                        (distinct emptyset emptyset))
                                   a!69))
                         (a!78 (or (<= (max emptyset) (+ (max S2_plus) 1))
                                   (and (= S2_plus emptyset) a!77)))
                         (a!81 (or (>= (max emptyset) (+ (max S2_plus) 1))
                                   (and (= S2_plus emptyset) a!80)))
                         (a!86 (or a!84
                                   false
                                   (and (>= (min emptyset) 0)
                                        (>= (max E_S2_minus) 1))
                                   (and (>= (min emptyset) 1)
                                        (>= (max E_S2_minus) 0))
                                   a!85))
                         (a!108 (or a!106
                                    false
                                    (and (>= (min E_S2_plus) 0)
                                         (>= (max E_S2_minus) 1))
                                    (and (>= (min E_S2_plus) 1)
                                         (>= (max E_S2_minus) 0))
                                    a!107))
                         (a!129 (or a!128
                                    false
                                    (and (>= (min emptyset) 0)
                                         (>= (max emptyset) 1))
                                    (and (>= (min emptyset) 1)
                                         (>= (max emptyset) 0))
                                    a!128)))
                   (let ((a!18 (and true
                                    (or a!13
                                        (and (= E_S2_plus emptyset)
                                             (distinct emptyset emptyset)
                                             (distinct S2_plus emptyset))
                                        a!14)
                                    (or a!16 a!17)))
                         (a!83 (and true
                                    (or a!78
                                        (and (= emptyset emptyset)
                                             (distinct E_S2_minus emptyset)
                                             (distinct S2_plus emptyset))
                                        a!79)
                                    (or a!81 a!82)))
                         (a!104 (or a!13
                                    (and (and (= E_S2_plus emptyset)
                                              (distinct E_S2_minus emptyset))
                                         (distinct S2_plus emptyset))
                                    a!103))
                         (a!127 (and true
                                     (or a!78
                                         (and (= emptyset emptyset)
                                              (distinct emptyset emptyset)
                                              (distinct S2_plus emptyset))
                                         a!125)
                                     (or a!81 a!126))))
                   (let ((a!33 (and (and (= S1_2_minus
                                            (setunion emptyset emptyset))
                                         a!1)
                                    (and (= emptyset
                                            (setunion S2_minus emptyset))
                                         a!2)
                                    (subset emptyset emptyset)
                                    (subset E_S2_plus E_S1_plus)
                                    (not (and (= S2_minus emptyset)
                                              (= S2_plus emptyset)))
                                    (not (and a!3 (not a!4)))
                                    (and true a!8 a!11)
                                    a!18
                                    (and true a!21)
                                    (and true a!24)
                                    (and true a!28)
                                    a!32
                                    (forall ((y_plus Int)
                                             (y_minus Int)
                                             (x_plus Int)
                                             (x_minus Int))
                                      (let ((a!1 (subset (set x_plus)
                                                         (setunion (setminus E_S1_plus
                                                                             E_S2_plus)
                                                                   (set (max E_S2_plus)))))
                                            (a!3 (subset (set y_plus)
                                                         (setunion (setminus E_S1_plus
                                                                             E_S2_plus)
                                                                   (set (max E_S2_plus)))))
                                            (a!5 (not (and true
                                                           (<= y_plus
                                                               (+ x_plus 1))
                                                           (>= y_plus
                                                               (+ x_plus 1)))))
                                            (a!8 (and (and true (= y_minus 0))
                                                      (and (= x_plus 0)
                                                           (> x_minus 0))))
                                            (a!9 (subset emptyset
                                                         (setunion (setminus E_S1_plus
                                                                             E_S2_plus)
                                                                   (set (max E_S2_plus)))))
                                            (a!11 (or false
                                                      (and (>= y_plus 0)
                                                           (>= x_minus 1))
                                                      (and (>= y_plus 1)
                                                           (>= x_minus 0))))
                                            (a!15 (and (and true
                                                            (= y_plus 0)
                                                            (> y_minus 0))
                                                       (= x_minus 0)))
                                            (a!19 (and (and true
                                                            (= y_plus 0)
                                                            (> y_minus 0))
                                                       (and (= x_plus 0)
                                                            (> x_minus 0))))
                                            (a!20 (not (and true
                                                            (<= x_minus
                                                                (+ y_minus 1))
                                                            (>= x_minus
                                                                (+ y_minus 1))))))
                                      (let ((a!2 (and (subset emptyset
                                                              (setunion (setminus emptyset
                                                                                  emptyset)
                                                                        emptyset))
                                                      a!1))
                                            (a!4 (and (subset emptyset
                                                              (setunion (setminus emptyset
                                                                                  emptyset)
                                                                        emptyset))
                                                      a!3))
                                            (a!10 (and (subset (set x_minus)
                                                               (setunion (setminus emptyset
                                                                                   emptyset)
                                                                         emptyset))
                                                       a!9))
                                            (a!12 (and true
                                                       (or false
                                                           (and (<= y_plus 0)
                                                                (<= x_minus 1))
                                                           (and (<= y_plus 1)
                                                                (<= x_minus 0)))
                                                       a!11))
                                            (a!16 (and (subset (set y_minus)
                                                               (setunion (setminus emptyset
                                                                                   emptyset)
                                                                         emptyset))
                                                       a!9)))
                                      (let ((a!6 (and a!2
                                                      a!4
                                                      (>= y_plus (+ x_plus 1))
                                                      (forall ((z_plus Int)
                                                               (z_minus Int))
                                                        (let ((a!1 (subset (set z_plus)
                                                                           (setunion (setminus E_S1_plus
                                                                                               E_S2_plus)
                                                                                     (set (max E_S2_plus)))))
                                                              (a!3 (and (>= z_plus
                                                                            (+ x_plus
                                                                               1))
                                                                        (>= y_plus
                                                                            (+ z_plus
                                                                               1))))
                                                              (a!5 (subset emptyset
                                                                           (setunion (setminus E_S1_plus
                                                                                               E_S2_plus)
                                                                                     (set (max E_S2_plus)))))
                                                              (a!7 (or false
                                                                       (and (>= y_plus
                                                                                0)
                                                                            (>= z_minus
                                                                                1))
                                                                       (and (>= y_plus
                                                                                1)
                                                                            (>= z_minus
                                                                                0)))))
                                                        (let ((a!2 (and (subset emptyset
                                                                                (setunion (setminus emptyset
                                                                                                    emptyset)
                                                                                          emptyset))
                                                                        a!1))
                                                              (a!6 (and (subset (set z_minus)
                                                                                (setunion (setminus emptyset
                                                                                                    emptyset)
                                                                                          emptyset))
                                                                        a!5)))
                                                        (let ((a!4 (and (and true
                                                                             (= z_minus
                                                                                0))
                                                                        (not (not (and a!2
                                                                                       a!3)))))
                                                              (a!8 (not (not (and a!6
                                                                                  (and false
                                                                                       a!7))))))
                                                        (let ((a!9 (and (and true
                                                                             (and (= z_plus
                                                                                     0)
                                                                                  (> z_minus
                                                                                     0)))
                                                                        a!8)))
                                                          (and (not a!4)
                                                               (not a!9)))))))
                                                      a!5))
                                            (a!13 (and a!10
                                                       a!4
                                                       a!11
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset (set z_plus)
                                                                            (setunion (setminus E_S1_plus
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!3 (or false
                                                                        (and (>= z_plus
                                                                                 0)
                                                                             (>= x_minus
                                                                                 1))
                                                                        (and (>= z_plus
                                                                                 1)
                                                                             (>= x_minus
                                                                                 0))))
                                                               (a!6 (subset emptyset
                                                                            (setunion (setminus E_S1_plus
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!8 (or false
                                                                        (and (>= y_plus
                                                                                 0)
                                                                             (>= z_minus
                                                                                 1))
                                                                        (and (>= y_plus
                                                                                 1)
                                                                             (>= z_minus
                                                                                 0)))))
                                                         (let ((a!2 (and (subset emptyset
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!1))
                                                               (a!7 (and (subset (set z_minus)
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!6)))
                                                         (let ((a!4 (and a!2
                                                                         (and a!3
                                                                              (>= y_plus
                                                                                  (+ z_plus
                                                                                     1)))))
                                                               (a!9 (and a!7
                                                                         (and (>= x_minus
                                                                                  (+ z_minus
                                                                                     1))
                                                                              a!8))))
                                                         (let ((a!5 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              (not (not a!4)))))
                                                               (a!10 (and (and true
                                                                               (and (= z_plus
                                                                                       0)
                                                                                    (> z_minus
                                                                                       0)))
                                                                          (not (not a!9)))))
                                                           (and a!5 (not a!10)))))))
                                                       (not a!12)))
                                            (a!17 (and a!2
                                                       a!16
                                                       false
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset (set z_plus)
                                                                            (setunion (setminus E_S1_plus
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!5 (subset emptyset
                                                                            (setunion (setminus E_S1_plus
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus))))))
                                                         (let ((a!2 (and (subset emptyset
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!1))
                                                               (a!6 (and (subset (set z_minus)
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!5)))
                                                         (let ((a!3 (and a!2
                                                                         (and (>= z_plus
                                                                                  (+ x_plus
                                                                                     1))
                                                                              false)))
                                                               (a!7 (and a!6
                                                                         (and false
                                                                              (>= z_minus
                                                                                  (+ y_minus
                                                                                     1))))))
                                                         (let ((a!4 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              (not (not a!3)))))
                                                               (a!8 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         (not (not a!7)))))
                                                           (and a!4 (not a!8)))))))
                                                       (not (and true
                                                                 true
                                                                 false))))
                                            (a!21 (and a!10
                                                       a!16
                                                       (>= x_minus
                                                           (+ y_minus 1))
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset (set z_plus)
                                                                            (setunion (setminus E_S1_plus
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!3 (or false
                                                                        (and (>= z_plus
                                                                                 0)
                                                                             (>= x_minus
                                                                                 1))
                                                                        (and (>= z_plus
                                                                                 1)
                                                                             (>= x_minus
                                                                                 0))))
                                                               (a!6 (subset emptyset
                                                                            (setunion (setminus E_S1_plus
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!8 (and (>= x_minus
                                                                             (+ z_minus
                                                                                1))
                                                                         (>= z_minus
                                                                             (+ y_minus
                                                                                1)))))
                                                         (let ((a!2 (and (subset emptyset
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!1))
                                                               (a!7 (and (subset (set z_minus)
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!6)))
                                                         (let ((a!4 (not (not (and a!2
                                                                                   (and a!3
                                                                                        false)))))
                                                               (a!9 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         (not (not (and a!7
                                                                                        a!8))))))
                                                         (let ((a!5 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              a!4))))
                                                           (and a!5 (not a!9)))))))
                                                       a!20)))
                                      (let ((a!7 (and (and (and true
                                                                (= y_minus 0))
                                                           (= x_minus 0))
                                                      (not (not a!6))))
                                            (a!14 (not (and a!8
                                                            (not (not a!13)))))
                                            (a!18 (not (and a!15
                                                            (not (not a!17)))))
                                            (a!22 (not (and a!19
                                                            (not (not a!21))))))
                                        (and (not a!7) a!14 a!18 a!22))))))))
                         (a!49 (and (and (= S1_2_minus
                                            (setunion E_S1_minus emptyset))
                                         a!35)
                                    (and (= emptyset
                                            (setunion S2_minus emptyset))
                                         a!2)
                                    (subset emptyset E_S1_minus)
                                    (subset E_S2_plus emptyset)
                                    (not (and (= S2_minus emptyset)
                                              (= S2_plus emptyset)))
                                    (not (and a!36 (not a!37)))
                                    (and true a!41 a!44)
                                    a!18
                                    (and true a!21)
                                    (and true a!24)
                                    (and true a!28)
                                    (and true a!48)
                                    (forall ((y_plus Int)
                                             (y_minus Int)
                                             (x_plus Int)
                                             (x_minus Int))
                                      (let ((a!1 (subset (set x_plus)
                                                         (setunion (setminus emptyset
                                                                             E_S2_plus)
                                                                   (set (max E_S2_plus)))))
                                            (a!3 (subset (set y_plus)
                                                         (setunion (setminus emptyset
                                                                             E_S2_plus)
                                                                   (set (max E_S2_plus)))))
                                            (a!5 (not (and true
                                                           (<= y_plus
                                                               (+ x_plus 1))
                                                           (>= y_plus
                                                               (+ x_plus 1)))))
                                            (a!8 (and (and true (= y_minus 0))
                                                      (and (= x_plus 0)
                                                           (> x_minus 0))))
                                            (a!9 (subset emptyset
                                                         (setunion (setminus emptyset
                                                                             E_S2_plus)
                                                                   (set (max E_S2_plus)))))
                                            (a!11 (or false
                                                      (and (>= y_plus 0)
                                                           (>= x_minus 1))
                                                      (and (>= y_plus 1)
                                                           (>= x_minus 0))))
                                            (a!15 (and (and true
                                                            (= y_plus 0)
                                                            (> y_minus 0))
                                                       (= x_minus 0)))
                                            (a!19 (and (and true
                                                            (= y_plus 0)
                                                            (> y_minus 0))
                                                       (and (= x_plus 0)
                                                            (> x_minus 0))))
                                            (a!20 (not (and true
                                                            (<= x_minus
                                                                (+ y_minus 1))
                                                            (>= x_minus
                                                                (+ y_minus 1))))))
                                      (let ((a!2 (and (subset emptyset
                                                              (setunion (setminus E_S1_minus
                                                                                  emptyset)
                                                                        emptyset))
                                                      a!1))
                                            (a!4 (and (subset emptyset
                                                              (setunion (setminus E_S1_minus
                                                                                  emptyset)
                                                                        emptyset))
                                                      a!3))
                                            (a!10 (and (subset (set x_minus)
                                                               (setunion (setminus E_S1_minus
                                                                                   emptyset)
                                                                         emptyset))
                                                       a!9))
                                            (a!12 (and true
                                                       (or false
                                                           (and (<= y_plus 0)
                                                                (<= x_minus 1))
                                                           (and (<= y_plus 1)
                                                                (<= x_minus 0)))
                                                       a!11))
                                            (a!16 (and (subset (set y_minus)
                                                               (setunion (setminus E_S1_minus
                                                                                   emptyset)
                                                                         emptyset))
                                                       a!9)))
                                      (let ((a!6 (and a!2
                                                      a!4
                                                      (>= y_plus (+ x_plus 1))
                                                      (forall ((z_plus Int)
                                                               (z_minus Int))
                                                        (let ((a!1 (subset (set z_plus)
                                                                           (setunion (setminus emptyset
                                                                                               E_S2_plus)
                                                                                     (set (max E_S2_plus)))))
                                                              (a!3 (and (>= z_plus
                                                                            (+ x_plus
                                                                               1))
                                                                        (>= y_plus
                                                                            (+ z_plus
                                                                               1))))
                                                              (a!5 (subset emptyset
                                                                           (setunion (setminus emptyset
                                                                                               E_S2_plus)
                                                                                     (set (max E_S2_plus)))))
                                                              (a!7 (or false
                                                                       (and (>= y_plus
                                                                                0)
                                                                            (>= z_minus
                                                                                1))
                                                                       (and (>= y_plus
                                                                                1)
                                                                            (>= z_minus
                                                                                0)))))
                                                        (let ((a!2 (and (subset emptyset
                                                                                (setunion (setminus E_S1_minus
                                                                                                    emptyset)
                                                                                          emptyset))
                                                                        a!1))
                                                              (a!6 (and (subset (set z_minus)
                                                                                (setunion (setminus E_S1_minus
                                                                                                    emptyset)
                                                                                          emptyset))
                                                                        a!5)))
                                                        (let ((a!4 (and (and true
                                                                             (= z_minus
                                                                                0))
                                                                        (not (not (and a!2
                                                                                       a!3)))))
                                                              (a!8 (not (not (and a!6
                                                                                  (and false
                                                                                       a!7))))))
                                                        (let ((a!9 (and (and true
                                                                             (and (= z_plus
                                                                                     0)
                                                                                  (> z_minus
                                                                                     0)))
                                                                        a!8)))
                                                          (and (not a!4)
                                                               (not a!9)))))))
                                                      a!5))
                                            (a!13 (and a!10
                                                       a!4
                                                       a!11
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset (set z_plus)
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!3 (or false
                                                                        (and (>= z_plus
                                                                                 0)
                                                                             (>= x_minus
                                                                                 1))
                                                                        (and (>= z_plus
                                                                                 1)
                                                                             (>= x_minus
                                                                                 0))))
                                                               (a!6 (subset emptyset
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!8 (or false
                                                                        (and (>= y_plus
                                                                                 0)
                                                                             (>= z_minus
                                                                                 1))
                                                                        (and (>= y_plus
                                                                                 1)
                                                                             (>= z_minus
                                                                                 0)))))
                                                         (let ((a!2 (and (subset emptyset
                                                                                 (setunion (setminus E_S1_minus
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!1))
                                                               (a!7 (and (subset (set z_minus)
                                                                                 (setunion (setminus E_S1_minus
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!6)))
                                                         (let ((a!4 (and a!2
                                                                         (and a!3
                                                                              (>= y_plus
                                                                                  (+ z_plus
                                                                                     1)))))
                                                               (a!9 (and a!7
                                                                         (and (>= x_minus
                                                                                  (+ z_minus
                                                                                     1))
                                                                              a!8))))
                                                         (let ((a!5 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              (not (not a!4)))))
                                                               (a!10 (and (and true
                                                                               (and (= z_plus
                                                                                       0)
                                                                                    (> z_minus
                                                                                       0)))
                                                                          (not (not a!9)))))
                                                           (and a!5 (not a!10)))))))
                                                       (not a!12)))
                                            (a!17 (and a!2
                                                       a!16
                                                       false
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset (set z_plus)
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!5 (subset emptyset
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus))))))
                                                         (let ((a!2 (and (subset emptyset
                                                                                 (setunion (setminus E_S1_minus
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!1))
                                                               (a!6 (and (subset (set z_minus)
                                                                                 (setunion (setminus E_S1_minus
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!5)))
                                                         (let ((a!3 (and a!2
                                                                         (and (>= z_plus
                                                                                  (+ x_plus
                                                                                     1))
                                                                              false)))
                                                               (a!7 (and a!6
                                                                         (and false
                                                                              (>= z_minus
                                                                                  (+ y_minus
                                                                                     1))))))
                                                         (let ((a!4 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              (not (not a!3)))))
                                                               (a!8 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         (not (not a!7)))))
                                                           (and a!4 (not a!8)))))))
                                                       (not (and true
                                                                 true
                                                                 false))))
                                            (a!21 (and a!10
                                                       a!16
                                                       (>= x_minus
                                                           (+ y_minus 1))
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset (set z_plus)
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!3 (or false
                                                                        (and (>= z_plus
                                                                                 0)
                                                                             (>= x_minus
                                                                                 1))
                                                                        (and (>= z_plus
                                                                                 1)
                                                                             (>= x_minus
                                                                                 0))))
                                                               (a!6 (subset emptyset
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!8 (and (>= x_minus
                                                                             (+ z_minus
                                                                                1))
                                                                         (>= z_minus
                                                                             (+ y_minus
                                                                                1)))))
                                                         (let ((a!2 (and (subset emptyset
                                                                                 (setunion (setminus E_S1_minus
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!1))
                                                               (a!7 (and (subset (set z_minus)
                                                                                 (setunion (setminus E_S1_minus
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!6)))
                                                         (let ((a!4 (not (not (and a!2
                                                                                   (and a!3
                                                                                        false)))))
                                                               (a!9 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         (not (not (and a!7
                                                                                        a!8))))))
                                                         (let ((a!5 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              a!4))))
                                                           (and a!5 (not a!9)))))))
                                                       a!20)))
                                      (let ((a!7 (and (and (and true
                                                                (= y_minus 0))
                                                           (= x_minus 0))
                                                      (not (not a!6))))
                                            (a!14 (not (and a!8
                                                            (not (not a!13)))))
                                            (a!18 (not (and a!15
                                                            (not (not a!17)))))
                                            (a!22 (not (and a!19
                                                            (not (not a!21))))))
                                        (and (not a!7) a!14 a!18 a!22))))))))
                         (a!61 (and (and (= S1_2_minus
                                            (setunion E_S1_minus emptyset))
                                         a!1)
                                    (and (= emptyset
                                            (setunion S2_minus emptyset))
                                         a!2)
                                    (subset emptyset E_S1_minus)
                                    (subset E_S2_plus E_S1_plus)
                                    (not (and (= S2_minus emptyset)
                                              (= S2_plus emptyset)))
                                    (not (and a!51 (not a!52)))
                                    (and true a!54 a!56)
                                    a!18
                                    (and true a!21)
                                    (and true a!24)
                                    (and true a!28)
                                    a!60
                                    (forall ((y_plus Int)
                                             (y_minus Int)
                                             (x_plus Int)
                                             (x_minus Int))
                                      (let ((a!1 (subset (set x_plus)
                                                         (setunion (setminus E_S1_plus
                                                                             E_S2_plus)
                                                                   (set (max E_S2_plus)))))
                                            (a!3 (subset (set y_plus)
                                                         (setunion (setminus E_S1_plus
                                                                             E_S2_plus)
                                                                   (set (max E_S2_plus)))))
                                            (a!5 (not (and true
                                                           (<= y_plus
                                                               (+ x_plus 1))
                                                           (>= y_plus
                                                               (+ x_plus 1)))))
                                            (a!8 (and (and true (= y_minus 0))
                                                      (and (= x_plus 0)
                                                           (> x_minus 0))))
                                            (a!9 (subset emptyset
                                                         (setunion (setminus E_S1_plus
                                                                             E_S2_plus)
                                                                   (set (max E_S2_plus)))))
                                            (a!11 (or false
                                                      (and (>= y_plus 0)
                                                           (>= x_minus 1))
                                                      (and (>= y_plus 1)
                                                           (>= x_minus 0))))
                                            (a!15 (and (and true
                                                            (= y_plus 0)
                                                            (> y_minus 0))
                                                       (= x_minus 0)))
                                            (a!19 (and (and true
                                                            (= y_plus 0)
                                                            (> y_minus 0))
                                                       (and (= x_plus 0)
                                                            (> x_minus 0))))
                                            (a!20 (not (and true
                                                            (<= x_minus
                                                                (+ y_minus 1))
                                                            (>= x_minus
                                                                (+ y_minus 1))))))
                                      (let ((a!2 (and (subset emptyset
                                                              (setunion (setminus E_S1_minus
                                                                                  emptyset)
                                                                        emptyset))
                                                      a!1))
                                            (a!4 (and (subset emptyset
                                                              (setunion (setminus E_S1_minus
                                                                                  emptyset)
                                                                        emptyset))
                                                      a!3))
                                            (a!10 (and (subset (set x_minus)
                                                               (setunion (setminus E_S1_minus
                                                                                   emptyset)
                                                                         emptyset))
                                                       a!9))
                                            (a!12 (and true
                                                       (or false
                                                           (and (<= y_plus 0)
                                                                (<= x_minus 1))
                                                           (and (<= y_plus 1)
                                                                (<= x_minus 0)))
                                                       a!11))
                                            (a!16 (and (subset (set y_minus)
                                                               (setunion (setminus E_S1_minus
                                                                                   emptyset)
                                                                         emptyset))
                                                       a!9)))
                                      (let ((a!6 (and a!2
                                                      a!4
                                                      (>= y_plus (+ x_plus 1))
                                                      (forall ((z_plus Int)
                                                               (z_minus Int))
                                                        (let ((a!1 (subset (set z_plus)
                                                                           (setunion (setminus E_S1_plus
                                                                                               E_S2_plus)
                                                                                     (set (max E_S2_plus)))))
                                                              (a!3 (and (>= z_plus
                                                                            (+ x_plus
                                                                               1))
                                                                        (>= y_plus
                                                                            (+ z_plus
                                                                               1))))
                                                              (a!5 (subset emptyset
                                                                           (setunion (setminus E_S1_plus
                                                                                               E_S2_plus)
                                                                                     (set (max E_S2_plus)))))
                                                              (a!7 (or false
                                                                       (and (>= y_plus
                                                                                0)
                                                                            (>= z_minus
                                                                                1))
                                                                       (and (>= y_plus
                                                                                1)
                                                                            (>= z_minus
                                                                                0)))))
                                                        (let ((a!2 (and (subset emptyset
                                                                                (setunion (setminus E_S1_minus
                                                                                                    emptyset)
                                                                                          emptyset))
                                                                        a!1))
                                                              (a!6 (and (subset (set z_minus)
                                                                                (setunion (setminus E_S1_minus
                                                                                                    emptyset)
                                                                                          emptyset))
                                                                        a!5)))
                                                        (let ((a!4 (and (and true
                                                                             (= z_minus
                                                                                0))
                                                                        (not (not (and a!2
                                                                                       a!3)))))
                                                              (a!8 (not (not (and a!6
                                                                                  (and false
                                                                                       a!7))))))
                                                        (let ((a!9 (and (and true
                                                                             (and (= z_plus
                                                                                     0)
                                                                                  (> z_minus
                                                                                     0)))
                                                                        a!8)))
                                                          (and (not a!4)
                                                               (not a!9)))))))
                                                      a!5))
                                            (a!13 (and a!10
                                                       a!4
                                                       a!11
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset (set z_plus)
                                                                            (setunion (setminus E_S1_plus
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!3 (or false
                                                                        (and (>= z_plus
                                                                                 0)
                                                                             (>= x_minus
                                                                                 1))
                                                                        (and (>= z_plus
                                                                                 1)
                                                                             (>= x_minus
                                                                                 0))))
                                                               (a!6 (subset emptyset
                                                                            (setunion (setminus E_S1_plus
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!8 (or false
                                                                        (and (>= y_plus
                                                                                 0)
                                                                             (>= z_minus
                                                                                 1))
                                                                        (and (>= y_plus
                                                                                 1)
                                                                             (>= z_minus
                                                                                 0)))))
                                                         (let ((a!2 (and (subset emptyset
                                                                                 (setunion (setminus E_S1_minus
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!1))
                                                               (a!7 (and (subset (set z_minus)
                                                                                 (setunion (setminus E_S1_minus
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!6)))
                                                         (let ((a!4 (and a!2
                                                                         (and a!3
                                                                              (>= y_plus
                                                                                  (+ z_plus
                                                                                     1)))))
                                                               (a!9 (and a!7
                                                                         (and (>= x_minus
                                                                                  (+ z_minus
                                                                                     1))
                                                                              a!8))))
                                                         (let ((a!5 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              (not (not a!4)))))
                                                               (a!10 (and (and true
                                                                               (and (= z_plus
                                                                                       0)
                                                                                    (> z_minus
                                                                                       0)))
                                                                          (not (not a!9)))))
                                                           (and a!5 (not a!10)))))))
                                                       (not a!12)))
                                            (a!17 (and a!2
                                                       a!16
                                                       false
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset (set z_plus)
                                                                            (setunion (setminus E_S1_plus
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!5 (subset emptyset
                                                                            (setunion (setminus E_S1_plus
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus))))))
                                                         (let ((a!2 (and (subset emptyset
                                                                                 (setunion (setminus E_S1_minus
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!1))
                                                               (a!6 (and (subset (set z_minus)
                                                                                 (setunion (setminus E_S1_minus
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!5)))
                                                         (let ((a!3 (and a!2
                                                                         (and (>= z_plus
                                                                                  (+ x_plus
                                                                                     1))
                                                                              false)))
                                                               (a!7 (and a!6
                                                                         (and false
                                                                              (>= z_minus
                                                                                  (+ y_minus
                                                                                     1))))))
                                                         (let ((a!4 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              (not (not a!3)))))
                                                               (a!8 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         (not (not a!7)))))
                                                           (and a!4 (not a!8)))))))
                                                       (not (and true
                                                                 true
                                                                 false))))
                                            (a!21 (and a!10
                                                       a!16
                                                       (>= x_minus
                                                           (+ y_minus 1))
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset (set z_plus)
                                                                            (setunion (setminus E_S1_plus
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!3 (or false
                                                                        (and (>= z_plus
                                                                                 0)
                                                                             (>= x_minus
                                                                                 1))
                                                                        (and (>= z_plus
                                                                                 1)
                                                                             (>= x_minus
                                                                                 0))))
                                                               (a!6 (subset emptyset
                                                                            (setunion (setminus E_S1_plus
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!8 (and (>= x_minus
                                                                             (+ z_minus
                                                                                1))
                                                                         (>= z_minus
                                                                             (+ y_minus
                                                                                1)))))
                                                         (let ((a!2 (and (subset emptyset
                                                                                 (setunion (setminus E_S1_minus
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!1))
                                                               (a!7 (and (subset (set z_minus)
                                                                                 (setunion (setminus E_S1_minus
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!6)))
                                                         (let ((a!4 (not (not (and a!2
                                                                                   (and a!3
                                                                                        false)))))
                                                               (a!9 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         (not (not (and a!7
                                                                                        a!8))))))
                                                         (let ((a!5 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              a!4))))
                                                           (and a!5 (not a!9)))))))
                                                       a!20)))
                                      (let ((a!7 (and (and (and true
                                                                (= y_minus 0))
                                                           (= x_minus 0))
                                                      (not (not a!6))))
                                            (a!14 (not (and a!8
                                                            (not (not a!13)))))
                                            (a!18 (not (and a!15
                                                            (not (not a!17)))))
                                            (a!22 (not (and a!19
                                                            (not (not a!21))))))
                                        (and (not a!7) a!14 a!18 a!22))))))))
                         (a!72 (and (and (= S1_2_minus
                                            (setunion emptyset emptyset))
                                         a!35)
                                    (and (= emptyset
                                            (setunion S2_minus emptyset))
                                         a!2)
                                    (subset emptyset emptyset)
                                    (subset E_S2_plus emptyset)
                                    (not (and (= S2_minus emptyset)
                                              (= S2_plus emptyset)))
                                    (not (and a!63 (not a!64)))
                                    (and true a!66 a!68)
                                    a!18
                                    (and true a!21)
                                    (and true a!24)
                                    (and true a!28)
                                    (and true a!71)
                                    (forall ((y_plus Int)
                                             (y_minus Int)
                                             (x_plus Int)
                                             (x_minus Int))
                                      (let ((a!1 (subset (set x_plus)
                                                         (setunion (setminus emptyset
                                                                             E_S2_plus)
                                                                   (set (max E_S2_plus)))))
                                            (a!3 (subset (set y_plus)
                                                         (setunion (setminus emptyset
                                                                             E_S2_plus)
                                                                   (set (max E_S2_plus)))))
                                            (a!5 (not (and true
                                                           (<= y_plus
                                                               (+ x_plus 1))
                                                           (>= y_plus
                                                               (+ x_plus 1)))))
                                            (a!8 (and (and true (= y_minus 0))
                                                      (and (= x_plus 0)
                                                           (> x_minus 0))))
                                            (a!9 (subset emptyset
                                                         (setunion (setminus emptyset
                                                                             E_S2_plus)
                                                                   (set (max E_S2_plus)))))
                                            (a!11 (or false
                                                      (and (>= y_plus 0)
                                                           (>= x_minus 1))
                                                      (and (>= y_plus 1)
                                                           (>= x_minus 0))))
                                            (a!15 (and (and true
                                                            (= y_plus 0)
                                                            (> y_minus 0))
                                                       (= x_minus 0)))
                                            (a!19 (and (and true
                                                            (= y_plus 0)
                                                            (> y_minus 0))
                                                       (and (= x_plus 0)
                                                            (> x_minus 0))))
                                            (a!20 (not (and true
                                                            (<= x_minus
                                                                (+ y_minus 1))
                                                            (>= x_minus
                                                                (+ y_minus 1))))))
                                      (let ((a!2 (and (subset emptyset
                                                              (setunion (setminus emptyset
                                                                                  emptyset)
                                                                        emptyset))
                                                      a!1))
                                            (a!4 (and (subset emptyset
                                                              (setunion (setminus emptyset
                                                                                  emptyset)
                                                                        emptyset))
                                                      a!3))
                                            (a!10 (and (subset (set x_minus)
                                                               (setunion (setminus emptyset
                                                                                   emptyset)
                                                                         emptyset))
                                                       a!9))
                                            (a!12 (and true
                                                       (or false
                                                           (and (<= y_plus 0)
                                                                (<= x_minus 1))
                                                           (and (<= y_plus 1)
                                                                (<= x_minus 0)))
                                                       a!11))
                                            (a!16 (and (subset (set y_minus)
                                                               (setunion (setminus emptyset
                                                                                   emptyset)
                                                                         emptyset))
                                                       a!9)))
                                      (let ((a!6 (and a!2
                                                      a!4
                                                      (>= y_plus (+ x_plus 1))
                                                      (forall ((z_plus Int)
                                                               (z_minus Int))
                                                        (let ((a!1 (subset (set z_plus)
                                                                           (setunion (setminus emptyset
                                                                                               E_S2_plus)
                                                                                     (set (max E_S2_plus)))))
                                                              (a!3 (and (>= z_plus
                                                                            (+ x_plus
                                                                               1))
                                                                        (>= y_plus
                                                                            (+ z_plus
                                                                               1))))
                                                              (a!5 (subset emptyset
                                                                           (setunion (setminus emptyset
                                                                                               E_S2_plus)
                                                                                     (set (max E_S2_plus)))))
                                                              (a!7 (or false
                                                                       (and (>= y_plus
                                                                                0)
                                                                            (>= z_minus
                                                                                1))
                                                                       (and (>= y_plus
                                                                                1)
                                                                            (>= z_minus
                                                                                0)))))
                                                        (let ((a!2 (and (subset emptyset
                                                                                (setunion (setminus emptyset
                                                                                                    emptyset)
                                                                                          emptyset))
                                                                        a!1))
                                                              (a!6 (and (subset (set z_minus)
                                                                                (setunion (setminus emptyset
                                                                                                    emptyset)
                                                                                          emptyset))
                                                                        a!5)))
                                                        (let ((a!4 (and (and true
                                                                             (= z_minus
                                                                                0))
                                                                        (not (not (and a!2
                                                                                       a!3)))))
                                                              (a!8 (not (not (and a!6
                                                                                  (and false
                                                                                       a!7))))))
                                                        (let ((a!9 (and (and true
                                                                             (and (= z_plus
                                                                                     0)
                                                                                  (> z_minus
                                                                                     0)))
                                                                        a!8)))
                                                          (and (not a!4)
                                                               (not a!9)))))))
                                                      a!5))
                                            (a!13 (and a!10
                                                       a!4
                                                       a!11
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset (set z_plus)
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!3 (or false
                                                                        (and (>= z_plus
                                                                                 0)
                                                                             (>= x_minus
                                                                                 1))
                                                                        (and (>= z_plus
                                                                                 1)
                                                                             (>= x_minus
                                                                                 0))))
                                                               (a!6 (subset emptyset
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!8 (or false
                                                                        (and (>= y_plus
                                                                                 0)
                                                                             (>= z_minus
                                                                                 1))
                                                                        (and (>= y_plus
                                                                                 1)
                                                                             (>= z_minus
                                                                                 0)))))
                                                         (let ((a!2 (and (subset emptyset
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!1))
                                                               (a!7 (and (subset (set z_minus)
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!6)))
                                                         (let ((a!4 (and a!2
                                                                         (and a!3
                                                                              (>= y_plus
                                                                                  (+ z_plus
                                                                                     1)))))
                                                               (a!9 (and a!7
                                                                         (and (>= x_minus
                                                                                  (+ z_minus
                                                                                     1))
                                                                              a!8))))
                                                         (let ((a!5 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              (not (not a!4)))))
                                                               (a!10 (and (and true
                                                                               (and (= z_plus
                                                                                       0)
                                                                                    (> z_minus
                                                                                       0)))
                                                                          (not (not a!9)))))
                                                           (and a!5 (not a!10)))))))
                                                       (not a!12)))
                                            (a!17 (and a!2
                                                       a!16
                                                       false
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset (set z_plus)
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!5 (subset emptyset
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus))))))
                                                         (let ((a!2 (and (subset emptyset
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!1))
                                                               (a!6 (and (subset (set z_minus)
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!5)))
                                                         (let ((a!3 (and a!2
                                                                         (and (>= z_plus
                                                                                  (+ x_plus
                                                                                     1))
                                                                              false)))
                                                               (a!7 (and a!6
                                                                         (and false
                                                                              (>= z_minus
                                                                                  (+ y_minus
                                                                                     1))))))
                                                         (let ((a!4 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              (not (not a!3)))))
                                                               (a!8 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         (not (not a!7)))))
                                                           (and a!4 (not a!8)))))))
                                                       (not (and true
                                                                 true
                                                                 false))))
                                            (a!21 (and a!10
                                                       a!16
                                                       (>= x_minus
                                                           (+ y_minus 1))
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset (set z_plus)
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!3 (or false
                                                                        (and (>= z_plus
                                                                                 0)
                                                                             (>= x_minus
                                                                                 1))
                                                                        (and (>= z_plus
                                                                                 1)
                                                                             (>= x_minus
                                                                                 0))))
                                                               (a!6 (subset emptyset
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!8 (and (>= x_minus
                                                                             (+ z_minus
                                                                                1))
                                                                         (>= z_minus
                                                                             (+ y_minus
                                                                                1)))))
                                                         (let ((a!2 (and (subset emptyset
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!1))
                                                               (a!7 (and (subset (set z_minus)
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset))
                                                                         a!6)))
                                                         (let ((a!4 (not (not (and a!2
                                                                                   (and a!3
                                                                                        false)))))
                                                               (a!9 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         (not (not (and a!7
                                                                                        a!8))))))
                                                         (let ((a!5 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              a!4))))
                                                           (and a!5 (not a!9)))))))
                                                       a!20)))
                                      (let ((a!7 (and (and (and true
                                                                (= y_minus 0))
                                                           (= x_minus 0))
                                                      (not (not a!6))))
                                            (a!14 (not (and a!8
                                                            (not (not a!13)))))
                                            (a!18 (not (and a!15
                                                            (not (not a!17)))))
                                            (a!22 (not (and a!19
                                                            (not (not a!21))))))
                                        (and (not a!7) a!14 a!18 a!22))))))))
                         (a!87 (and (and (= S1_2_minus
                                            (setunion emptyset emptyset))
                                         a!1)
                                    (and a!74
                                         (= emptyset
                                            (setunion S2_plus emptyset)))
                                    (subset E_S2_minus emptyset)
                                    (subset emptyset E_S1_plus)
                                    (not (and (= S2_minus emptyset)
                                              (= S2_plus emptyset)))
                                    (not (and a!75 (not a!76)))
                                    (and true a!8 a!11)
                                    a!83
                                    (and true a!21)
                                    (and true a!86)
                                    (and true a!28)
                                    a!32
                                    (forall ((y_plus Int)
                                             (y_minus Int)
                                             (x_plus Int)
                                             (x_minus Int))
                                      (let ((a!1 (subset emptyset
                                                         (setunion (setminus emptyset
                                                                             E_S2_minus)
                                                                   (set (min E_S2_minus)))))
                                            (a!4 (not (and true
                                                           (<= y_plus
                                                               (+ x_plus 1))
                                                           (>= y_plus
                                                               (+ x_plus 1)))))
                                            (a!7 (and (and true (= y_minus 0))
                                                      (and (= x_plus 0)
                                                           (> x_minus 0))))
                                            (a!8 (subset (set x_minus)
                                                         (setunion (setminus emptyset
                                                                             E_S2_minus)
                                                                   (set (min E_S2_minus)))))
                                            (a!10 (or false
                                                      (and (>= y_plus 0)
                                                           (>= x_minus 1))
                                                      (and (>= y_plus 1)
                                                           (>= x_minus 0))))
                                            (a!14 (and (and true
                                                            (= y_plus 0)
                                                            (> y_minus 0))
                                                       (= x_minus 0)))
                                            (a!15 (subset (set y_minus)
                                                          (setunion (setminus emptyset
                                                                              E_S2_minus)
                                                                    (set (min E_S2_minus)))))
                                            (a!19 (and (and true
                                                            (= y_plus 0)
                                                            (> y_minus 0))
                                                       (and (= x_plus 0)
                                                            (> x_minus 0))))
                                            (a!20 (not (and true
                                                            (<= x_minus
                                                                (+ y_minus 1))
                                                            (>= x_minus
                                                                (+ y_minus 1))))))
                                      (let ((a!2 (and a!1
                                                      (subset (set x_plus)
                                                              (setunion (setminus E_S1_plus
                                                                                  emptyset)
                                                                        emptyset))))
                                            (a!3 (and a!1
                                                      (subset (set y_plus)
                                                              (setunion (setminus E_S1_plus
                                                                                  emptyset)
                                                                        emptyset))))
                                            (a!9 (and a!8
                                                      (subset emptyset
                                                              (setunion (setminus E_S1_plus
                                                                                  emptyset)
                                                                        emptyset))))
                                            (a!11 (and true
                                                       (or false
                                                           (and (<= y_plus 0)
                                                                (<= x_minus 1))
                                                           (and (<= y_plus 1)
                                                                (<= x_minus 0)))
                                                       a!10))
                                            (a!16 (and a!15
                                                       (subset emptyset
                                                               (setunion (setminus E_S1_plus
                                                                                   emptyset)
                                                                         emptyset)))))
                                      (let ((a!5 (and a!2
                                                      a!3
                                                      (>= y_plus (+ x_plus 1))
                                                      (forall ((z_plus Int)
                                                               (z_minus Int))
                                                        (let ((a!1 (subset emptyset
                                                                           (setunion (setminus emptyset
                                                                                               E_S2_minus)
                                                                                     (set (min E_S2_minus)))))
                                                              (a!3 (and (>= z_plus
                                                                            (+ x_plus
                                                                               1))
                                                                        (>= y_plus
                                                                            (+ z_plus
                                                                               1))))
                                                              (a!5 (subset (set z_minus)
                                                                           (setunion (setminus emptyset
                                                                                               E_S2_minus)
                                                                                     (set (min E_S2_minus)))))
                                                              (a!7 (or false
                                                                       (and (>= y_plus
                                                                                0)
                                                                            (>= z_minus
                                                                                1))
                                                                       (and (>= y_plus
                                                                                1)
                                                                            (>= z_minus
                                                                                0)))))
                                                        (let ((a!2 (and a!1
                                                                        (subset (set z_plus)
                                                                                (setunion (setminus E_S1_plus
                                                                                                    emptyset)
                                                                                          emptyset))))
                                                              (a!6 (and a!5
                                                                        (subset emptyset
                                                                                (setunion (setminus E_S1_plus
                                                                                                    emptyset)
                                                                                          emptyset)))))
                                                        (let ((a!4 (and (and true
                                                                             (= z_minus
                                                                                0))
                                                                        (not (not (and a!2
                                                                                       a!3)))))
                                                              (a!8 (not (not (and a!6
                                                                                  (and false
                                                                                       a!7))))))
                                                        (let ((a!9 (and (and true
                                                                             (and (= z_plus
                                                                                     0)
                                                                                  (> z_minus
                                                                                     0)))
                                                                        a!8)))
                                                          (and (not a!4)
                                                               (not a!9)))))))
                                                      a!4))
                                            (a!12 (and a!9
                                                       a!3
                                                       a!10
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset emptyset
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!3 (or false
                                                                        (and (>= z_plus
                                                                                 0)
                                                                             (>= x_minus
                                                                                 1))
                                                                        (and (>= z_plus
                                                                                 1)
                                                                             (>= x_minus
                                                                                 0))))
                                                               (a!6 (subset (set z_minus)
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!8 (or false
                                                                        (and (>= y_plus
                                                                                 0)
                                                                             (>= z_minus
                                                                                 1))
                                                                        (and (>= y_plus
                                                                                 1)
                                                                             (>= z_minus
                                                                                 0)))))
                                                         (let ((a!2 (and a!1
                                                                         (subset (set z_plus)
                                                                                 (setunion (setminus E_S1_plus
                                                                                                     emptyset)
                                                                                           emptyset))))
                                                               (a!7 (and a!6
                                                                         (subset emptyset
                                                                                 (setunion (setminus E_S1_plus
                                                                                                     emptyset)
                                                                                           emptyset)))))
                                                         (let ((a!4 (and a!2
                                                                         (and a!3
                                                                              (>= y_plus
                                                                                  (+ z_plus
                                                                                     1)))))
                                                               (a!9 (and a!7
                                                                         (and (>= x_minus
                                                                                  (+ z_minus
                                                                                     1))
                                                                              a!8))))
                                                         (let ((a!5 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              (not (not a!4)))))
                                                               (a!10 (and (and true
                                                                               (and (= z_plus
                                                                                       0)
                                                                                    (> z_minus
                                                                                       0)))
                                                                          (not (not a!9)))))
                                                           (and a!5 (not a!10)))))))
                                                       (not a!11)))
                                            (a!17 (and a!2
                                                       a!16
                                                       false
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset emptyset
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!5 (subset (set z_minus)
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus))))))
                                                         (let ((a!2 (and a!1
                                                                         (subset (set z_plus)
                                                                                 (setunion (setminus E_S1_plus
                                                                                                     emptyset)
                                                                                           emptyset))))
                                                               (a!6 (and a!5
                                                                         (subset emptyset
                                                                                 (setunion (setminus E_S1_plus
                                                                                                     emptyset)
                                                                                           emptyset)))))
                                                         (let ((a!3 (and a!2
                                                                         (and (>= z_plus
                                                                                  (+ x_plus
                                                                                     1))
                                                                              false)))
                                                               (a!7 (and a!6
                                                                         (and false
                                                                              (>= z_minus
                                                                                  (+ y_minus
                                                                                     1))))))
                                                         (let ((a!4 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              (not (not a!3)))))
                                                               (a!8 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         (not (not a!7)))))
                                                           (and a!4 (not a!8)))))))
                                                       (not (and true
                                                                 true
                                                                 false))))
                                            (a!21 (and a!9
                                                       a!16
                                                       (>= x_minus
                                                           (+ y_minus 1))
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset emptyset
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!3 (or false
                                                                        (and (>= z_plus
                                                                                 0)
                                                                             (>= x_minus
                                                                                 1))
                                                                        (and (>= z_plus
                                                                                 1)
                                                                             (>= x_minus
                                                                                 0))))
                                                               (a!6 (subset (set z_minus)
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!8 (and (>= x_minus
                                                                             (+ z_minus
                                                                                1))
                                                                         (>= z_minus
                                                                             (+ y_minus
                                                                                1)))))
                                                         (let ((a!2 (and a!1
                                                                         (subset (set z_plus)
                                                                                 (setunion (setminus E_S1_plus
                                                                                                     emptyset)
                                                                                           emptyset))))
                                                               (a!7 (and a!6
                                                                         (subset emptyset
                                                                                 (setunion (setminus E_S1_plus
                                                                                                     emptyset)
                                                                                           emptyset)))))
                                                         (let ((a!4 (not (not (and a!2
                                                                                   (and a!3
                                                                                        false)))))
                                                               (a!9 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         (not (not (and a!7
                                                                                        a!8))))))
                                                         (let ((a!5 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              a!4))))
                                                           (and a!5 (not a!9)))))))
                                                       a!20)))
                                      (let ((a!6 (and (and (and true
                                                                (= y_minus 0))
                                                           (= x_minus 0))
                                                      (not (not a!5))))
                                            (a!13 (not (and a!7
                                                            (not (not a!12)))))
                                            (a!18 (not (and a!14
                                                            (not (not a!17)))))
                                            (a!22 (not (and a!19
                                                            (not (not a!21))))))
                                        (and (not a!6) a!13 a!18 a!22))))))))
                         (a!91 (and (and (= S1_2_minus
                                            (setunion E_S1_minus emptyset))
                                         a!35)
                                    (and a!74
                                         (= emptyset
                                            (setunion S2_plus emptyset)))
                                    (subset E_S2_minus E_S1_minus)
                                    (subset emptyset emptyset)
                                    (not (and (= S2_minus emptyset)
                                              (= S2_plus emptyset)))
                                    (not (and a!89 (not a!90)))
                                    (and true a!41 a!44)
                                    a!83
                                    (and true a!21)
                                    (and true a!86)
                                    (and true a!28)
                                    (and true a!48)
                                    (forall ((y_plus Int)
                                             (y_minus Int)
                                             (x_plus Int)
                                             (x_minus Int))
                                      (let ((a!1 (subset emptyset
                                                         (setunion (setminus E_S1_minus
                                                                             E_S2_minus)
                                                                   (set (min E_S2_minus)))))
                                            (a!4 (not (and true
                                                           (<= y_plus
                                                               (+ x_plus 1))
                                                           (>= y_plus
                                                               (+ x_plus 1)))))
                                            (a!7 (and (and true (= y_minus 0))
                                                      (and (= x_plus 0)
                                                           (> x_minus 0))))
                                            (a!8 (subset (set x_minus)
                                                         (setunion (setminus E_S1_minus
                                                                             E_S2_minus)
                                                                   (set (min E_S2_minus)))))
                                            (a!10 (or false
                                                      (and (>= y_plus 0)
                                                           (>= x_minus 1))
                                                      (and (>= y_plus 1)
                                                           (>= x_minus 0))))
                                            (a!14 (and (and true
                                                            (= y_plus 0)
                                                            (> y_minus 0))
                                                       (= x_minus 0)))
                                            (a!15 (subset (set y_minus)
                                                          (setunion (setminus E_S1_minus
                                                                              E_S2_minus)
                                                                    (set (min E_S2_minus)))))
                                            (a!19 (and (and true
                                                            (= y_plus 0)
                                                            (> y_minus 0))
                                                       (and (= x_plus 0)
                                                            (> x_minus 0))))
                                            (a!20 (not (and true
                                                            (<= x_minus
                                                                (+ y_minus 1))
                                                            (>= x_minus
                                                                (+ y_minus 1))))))
                                      (let ((a!2 (and a!1
                                                      (subset (set x_plus)
                                                              (setunion (setminus emptyset
                                                                                  emptyset)
                                                                        emptyset))))
                                            (a!3 (and a!1
                                                      (subset (set y_plus)
                                                              (setunion (setminus emptyset
                                                                                  emptyset)
                                                                        emptyset))))
                                            (a!9 (and a!8
                                                      (subset emptyset
                                                              (setunion (setminus emptyset
                                                                                  emptyset)
                                                                        emptyset))))
                                            (a!11 (and true
                                                       (or false
                                                           (and (<= y_plus 0)
                                                                (<= x_minus 1))
                                                           (and (<= y_plus 1)
                                                                (<= x_minus 0)))
                                                       a!10))
                                            (a!16 (and a!15
                                                       (subset emptyset
                                                               (setunion (setminus emptyset
                                                                                   emptyset)
                                                                         emptyset)))))
                                      (let ((a!5 (and a!2
                                                      a!3
                                                      (>= y_plus (+ x_plus 1))
                                                      (forall ((z_plus Int)
                                                               (z_minus Int))
                                                        (let ((a!1 (subset emptyset
                                                                           (setunion (setminus E_S1_minus
                                                                                               E_S2_minus)
                                                                                     (set (min E_S2_minus)))))
                                                              (a!3 (and (>= z_plus
                                                                            (+ x_plus
                                                                               1))
                                                                        (>= y_plus
                                                                            (+ z_plus
                                                                               1))))
                                                              (a!5 (subset (set z_minus)
                                                                           (setunion (setminus E_S1_minus
                                                                                               E_S2_minus)
                                                                                     (set (min E_S2_minus)))))
                                                              (a!7 (or false
                                                                       (and (>= y_plus
                                                                                0)
                                                                            (>= z_minus
                                                                                1))
                                                                       (and (>= y_plus
                                                                                1)
                                                                            (>= z_minus
                                                                                0)))))
                                                        (let ((a!2 (and a!1
                                                                        (subset (set z_plus)
                                                                                (setunion (setminus emptyset
                                                                                                    emptyset)
                                                                                          emptyset))))
                                                              (a!6 (and a!5
                                                                        (subset emptyset
                                                                                (setunion (setminus emptyset
                                                                                                    emptyset)
                                                                                          emptyset)))))
                                                        (let ((a!4 (and (and true
                                                                             (= z_minus
                                                                                0))
                                                                        (not (not (and a!2
                                                                                       a!3)))))
                                                              (a!8 (not (not (and a!6
                                                                                  (and false
                                                                                       a!7))))))
                                                        (let ((a!9 (and (and true
                                                                             (and (= z_plus
                                                                                     0)
                                                                                  (> z_minus
                                                                                     0)))
                                                                        a!8)))
                                                          (and (not a!4)
                                                               (not a!9)))))))
                                                      a!4))
                                            (a!12 (and a!9
                                                       a!3
                                                       a!10
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset emptyset
                                                                            (setunion (setminus E_S1_minus
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!3 (or false
                                                                        (and (>= z_plus
                                                                                 0)
                                                                             (>= x_minus
                                                                                 1))
                                                                        (and (>= z_plus
                                                                                 1)
                                                                             (>= x_minus
                                                                                 0))))
                                                               (a!6 (subset (set z_minus)
                                                                            (setunion (setminus E_S1_minus
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!8 (or false
                                                                        (and (>= y_plus
                                                                                 0)
                                                                             (>= z_minus
                                                                                 1))
                                                                        (and (>= y_plus
                                                                                 1)
                                                                             (>= z_minus
                                                                                 0)))))
                                                         (let ((a!2 (and a!1
                                                                         (subset (set z_plus)
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset))))
                                                               (a!7 (and a!6
                                                                         (subset emptyset
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset)))))
                                                         (let ((a!4 (and a!2
                                                                         (and a!3
                                                                              (>= y_plus
                                                                                  (+ z_plus
                                                                                     1)))))
                                                               (a!9 (and a!7
                                                                         (and (>= x_minus
                                                                                  (+ z_minus
                                                                                     1))
                                                                              a!8))))
                                                         (let ((a!5 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              (not (not a!4)))))
                                                               (a!10 (and (and true
                                                                               (and (= z_plus
                                                                                       0)
                                                                                    (> z_minus
                                                                                       0)))
                                                                          (not (not a!9)))))
                                                           (and a!5 (not a!10)))))))
                                                       (not a!11)))
                                            (a!17 (and a!2
                                                       a!16
                                                       false
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset emptyset
                                                                            (setunion (setminus E_S1_minus
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!5 (subset (set z_minus)
                                                                            (setunion (setminus E_S1_minus
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus))))))
                                                         (let ((a!2 (and a!1
                                                                         (subset (set z_plus)
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset))))
                                                               (a!6 (and a!5
                                                                         (subset emptyset
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset)))))
                                                         (let ((a!3 (and a!2
                                                                         (and (>= z_plus
                                                                                  (+ x_plus
                                                                                     1))
                                                                              false)))
                                                               (a!7 (and a!6
                                                                         (and false
                                                                              (>= z_minus
                                                                                  (+ y_minus
                                                                                     1))))))
                                                         (let ((a!4 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              (not (not a!3)))))
                                                               (a!8 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         (not (not a!7)))))
                                                           (and a!4 (not a!8)))))))
                                                       (not (and true
                                                                 true
                                                                 false))))
                                            (a!21 (and a!9
                                                       a!16
                                                       (>= x_minus
                                                           (+ y_minus 1))
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset emptyset
                                                                            (setunion (setminus E_S1_minus
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!3 (or false
                                                                        (and (>= z_plus
                                                                                 0)
                                                                             (>= x_minus
                                                                                 1))
                                                                        (and (>= z_plus
                                                                                 1)
                                                                             (>= x_minus
                                                                                 0))))
                                                               (a!6 (subset (set z_minus)
                                                                            (setunion (setminus E_S1_minus
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!8 (and (>= x_minus
                                                                             (+ z_minus
                                                                                1))
                                                                         (>= z_minus
                                                                             (+ y_minus
                                                                                1)))))
                                                         (let ((a!2 (and a!1
                                                                         (subset (set z_plus)
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset))))
                                                               (a!7 (and a!6
                                                                         (subset emptyset
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset)))))
                                                         (let ((a!4 (not (not (and a!2
                                                                                   (and a!3
                                                                                        false)))))
                                                               (a!9 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         (not (not (and a!7
                                                                                        a!8))))))
                                                         (let ((a!5 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              a!4))))
                                                           (and a!5 (not a!9)))))))
                                                       a!20)))
                                      (let ((a!6 (and (and (and true
                                                                (= y_minus 0))
                                                           (= x_minus 0))
                                                      (not (not a!5))))
                                            (a!13 (not (and a!7
                                                            (not (not a!12)))))
                                            (a!18 (not (and a!14
                                                            (not (not a!17)))))
                                            (a!22 (not (and a!19
                                                            (not (not a!21))))))
                                        (and (not a!6) a!13 a!18 a!22))))))))
                         (a!95 (and (and (= S1_2_minus
                                            (setunion E_S1_minus emptyset))
                                         a!1)
                                    (and a!74
                                         (= emptyset
                                            (setunion S2_plus emptyset)))
                                    (subset E_S2_minus E_S1_minus)
                                    (subset emptyset E_S1_plus)
                                    (not (and (= S2_minus emptyset)
                                              (= S2_plus emptyset)))
                                    (not (and a!93 (not a!94)))
                                    (and true a!54 a!56)
                                    a!83
                                    (and true a!21)
                                    (and true a!86)
                                    (and true a!28)
                                    a!60
                                    (forall ((y_plus Int)
                                             (y_minus Int)
                                             (x_plus Int)
                                             (x_minus Int))
                                      (let ((a!1 (subset emptyset
                                                         (setunion (setminus E_S1_minus
                                                                             E_S2_minus)
                                                                   (set (min E_S2_minus)))))
                                            (a!4 (not (and true
                                                           (<= y_plus
                                                               (+ x_plus 1))
                                                           (>= y_plus
                                                               (+ x_plus 1)))))
                                            (a!7 (and (and true (= y_minus 0))
                                                      (and (= x_plus 0)
                                                           (> x_minus 0))))
                                            (a!8 (subset (set x_minus)
                                                         (setunion (setminus E_S1_minus
                                                                             E_S2_minus)
                                                                   (set (min E_S2_minus)))))
                                            (a!10 (or false
                                                      (and (>= y_plus 0)
                                                           (>= x_minus 1))
                                                      (and (>= y_plus 1)
                                                           (>= x_minus 0))))
                                            (a!14 (and (and true
                                                            (= y_plus 0)
                                                            (> y_minus 0))
                                                       (= x_minus 0)))
                                            (a!15 (subset (set y_minus)
                                                          (setunion (setminus E_S1_minus
                                                                              E_S2_minus)
                                                                    (set (min E_S2_minus)))))
                                            (a!19 (and (and true
                                                            (= y_plus 0)
                                                            (> y_minus 0))
                                                       (and (= x_plus 0)
                                                            (> x_minus 0))))
                                            (a!20 (not (and true
                                                            (<= x_minus
                                                                (+ y_minus 1))
                                                            (>= x_minus
                                                                (+ y_minus 1))))))
                                      (let ((a!2 (and a!1
                                                      (subset (set x_plus)
                                                              (setunion (setminus E_S1_plus
                                                                                  emptyset)
                                                                        emptyset))))
                                            (a!3 (and a!1
                                                      (subset (set y_plus)
                                                              (setunion (setminus E_S1_plus
                                                                                  emptyset)
                                                                        emptyset))))
                                            (a!9 (and a!8
                                                      (subset emptyset
                                                              (setunion (setminus E_S1_plus
                                                                                  emptyset)
                                                                        emptyset))))
                                            (a!11 (and true
                                                       (or false
                                                           (and (<= y_plus 0)
                                                                (<= x_minus 1))
                                                           (and (<= y_plus 1)
                                                                (<= x_minus 0)))
                                                       a!10))
                                            (a!16 (and a!15
                                                       (subset emptyset
                                                               (setunion (setminus E_S1_plus
                                                                                   emptyset)
                                                                         emptyset)))))
                                      (let ((a!5 (and a!2
                                                      a!3
                                                      (>= y_plus (+ x_plus 1))
                                                      (forall ((z_plus Int)
                                                               (z_minus Int))
                                                        (let ((a!1 (subset emptyset
                                                                           (setunion (setminus E_S1_minus
                                                                                               E_S2_minus)
                                                                                     (set (min E_S2_minus)))))
                                                              (a!3 (and (>= z_plus
                                                                            (+ x_plus
                                                                               1))
                                                                        (>= y_plus
                                                                            (+ z_plus
                                                                               1))))
                                                              (a!5 (subset (set z_minus)
                                                                           (setunion (setminus E_S1_minus
                                                                                               E_S2_minus)
                                                                                     (set (min E_S2_minus)))))
                                                              (a!7 (or false
                                                                       (and (>= y_plus
                                                                                0)
                                                                            (>= z_minus
                                                                                1))
                                                                       (and (>= y_plus
                                                                                1)
                                                                            (>= z_minus
                                                                                0)))))
                                                        (let ((a!2 (and a!1
                                                                        (subset (set z_plus)
                                                                                (setunion (setminus E_S1_plus
                                                                                                    emptyset)
                                                                                          emptyset))))
                                                              (a!6 (and a!5
                                                                        (subset emptyset
                                                                                (setunion (setminus E_S1_plus
                                                                                                    emptyset)
                                                                                          emptyset)))))
                                                        (let ((a!4 (and (and true
                                                                             (= z_minus
                                                                                0))
                                                                        (not (not (and a!2
                                                                                       a!3)))))
                                                              (a!8 (not (not (and a!6
                                                                                  (and false
                                                                                       a!7))))))
                                                        (let ((a!9 (and (and true
                                                                             (and (= z_plus
                                                                                     0)
                                                                                  (> z_minus
                                                                                     0)))
                                                                        a!8)))
                                                          (and (not a!4)
                                                               (not a!9)))))))
                                                      a!4))
                                            (a!12 (and a!9
                                                       a!3
                                                       a!10
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset emptyset
                                                                            (setunion (setminus E_S1_minus
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!3 (or false
                                                                        (and (>= z_plus
                                                                                 0)
                                                                             (>= x_minus
                                                                                 1))
                                                                        (and (>= z_plus
                                                                                 1)
                                                                             (>= x_minus
                                                                                 0))))
                                                               (a!6 (subset (set z_minus)
                                                                            (setunion (setminus E_S1_minus
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!8 (or false
                                                                        (and (>= y_plus
                                                                                 0)
                                                                             (>= z_minus
                                                                                 1))
                                                                        (and (>= y_plus
                                                                                 1)
                                                                             (>= z_minus
                                                                                 0)))))
                                                         (let ((a!2 (and a!1
                                                                         (subset (set z_plus)
                                                                                 (setunion (setminus E_S1_plus
                                                                                                     emptyset)
                                                                                           emptyset))))
                                                               (a!7 (and a!6
                                                                         (subset emptyset
                                                                                 (setunion (setminus E_S1_plus
                                                                                                     emptyset)
                                                                                           emptyset)))))
                                                         (let ((a!4 (and a!2
                                                                         (and a!3
                                                                              (>= y_plus
                                                                                  (+ z_plus
                                                                                     1)))))
                                                               (a!9 (and a!7
                                                                         (and (>= x_minus
                                                                                  (+ z_minus
                                                                                     1))
                                                                              a!8))))
                                                         (let ((a!5 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              (not (not a!4)))))
                                                               (a!10 (and (and true
                                                                               (and (= z_plus
                                                                                       0)
                                                                                    (> z_minus
                                                                                       0)))
                                                                          (not (not a!9)))))
                                                           (and a!5 (not a!10)))))))
                                                       (not a!11)))
                                            (a!17 (and a!2
                                                       a!16
                                                       false
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset emptyset
                                                                            (setunion (setminus E_S1_minus
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!5 (subset (set z_minus)
                                                                            (setunion (setminus E_S1_minus
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus))))))
                                                         (let ((a!2 (and a!1
                                                                         (subset (set z_plus)
                                                                                 (setunion (setminus E_S1_plus
                                                                                                     emptyset)
                                                                                           emptyset))))
                                                               (a!6 (and a!5
                                                                         (subset emptyset
                                                                                 (setunion (setminus E_S1_plus
                                                                                                     emptyset)
                                                                                           emptyset)))))
                                                         (let ((a!3 (and a!2
                                                                         (and (>= z_plus
                                                                                  (+ x_plus
                                                                                     1))
                                                                              false)))
                                                               (a!7 (and a!6
                                                                         (and false
                                                                              (>= z_minus
                                                                                  (+ y_minus
                                                                                     1))))))
                                                         (let ((a!4 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              (not (not a!3)))))
                                                               (a!8 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         (not (not a!7)))))
                                                           (and a!4 (not a!8)))))))
                                                       (not (and true
                                                                 true
                                                                 false))))
                                            (a!21 (and a!9
                                                       a!16
                                                       (>= x_minus
                                                           (+ y_minus 1))
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset emptyset
                                                                            (setunion (setminus E_S1_minus
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!3 (or false
                                                                        (and (>= z_plus
                                                                                 0)
                                                                             (>= x_minus
                                                                                 1))
                                                                        (and (>= z_plus
                                                                                 1)
                                                                             (>= x_minus
                                                                                 0))))
                                                               (a!6 (subset (set z_minus)
                                                                            (setunion (setminus E_S1_minus
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!8 (and (>= x_minus
                                                                             (+ z_minus
                                                                                1))
                                                                         (>= z_minus
                                                                             (+ y_minus
                                                                                1)))))
                                                         (let ((a!2 (and a!1
                                                                         (subset (set z_plus)
                                                                                 (setunion (setminus E_S1_plus
                                                                                                     emptyset)
                                                                                           emptyset))))
                                                               (a!7 (and a!6
                                                                         (subset emptyset
                                                                                 (setunion (setminus E_S1_plus
                                                                                                     emptyset)
                                                                                           emptyset)))))
                                                         (let ((a!4 (not (not (and a!2
                                                                                   (and a!3
                                                                                        false)))))
                                                               (a!9 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         (not (not (and a!7
                                                                                        a!8))))))
                                                         (let ((a!5 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              a!4))))
                                                           (and a!5 (not a!9)))))))
                                                       a!20)))
                                      (let ((a!6 (and (and (and true
                                                                (= y_minus 0))
                                                           (= x_minus 0))
                                                      (not (not a!5))))
                                            (a!13 (not (and a!7
                                                            (not (not a!12)))))
                                            (a!18 (not (and a!14
                                                            (not (not a!17)))))
                                            (a!22 (not (and a!19
                                                            (not (not a!21))))))
                                        (and (not a!6) a!13 a!18 a!22))))))))
                         (a!99 (and (and (= S1_2_minus
                                            (setunion emptyset emptyset))
                                         a!35)
                                    (and a!74
                                         (= emptyset
                                            (setunion S2_plus emptyset)))
                                    (subset E_S2_minus emptyset)
                                    (subset emptyset emptyset)
                                    (not (and (= S2_minus emptyset)
                                              (= S2_plus emptyset)))
                                    (not (and a!97 (not a!98)))
                                    (and true a!66 a!68)
                                    a!83
                                    (and true a!21)
                                    (and true a!86)
                                    (and true a!28)
                                    (and true a!71)
                                    (forall ((y_plus Int)
                                             (y_minus Int)
                                             (x_plus Int)
                                             (x_minus Int))
                                      (let ((a!1 (subset emptyset
                                                         (setunion (setminus emptyset
                                                                             E_S2_minus)
                                                                   (set (min E_S2_minus)))))
                                            (a!4 (not (and true
                                                           (<= y_plus
                                                               (+ x_plus 1))
                                                           (>= y_plus
                                                               (+ x_plus 1)))))
                                            (a!7 (and (and true (= y_minus 0))
                                                      (and (= x_plus 0)
                                                           (> x_minus 0))))
                                            (a!8 (subset (set x_minus)
                                                         (setunion (setminus emptyset
                                                                             E_S2_minus)
                                                                   (set (min E_S2_minus)))))
                                            (a!10 (or false
                                                      (and (>= y_plus 0)
                                                           (>= x_minus 1))
                                                      (and (>= y_plus 1)
                                                           (>= x_minus 0))))
                                            (a!14 (and (and true
                                                            (= y_plus 0)
                                                            (> y_minus 0))
                                                       (= x_minus 0)))
                                            (a!15 (subset (set y_minus)
                                                          (setunion (setminus emptyset
                                                                              E_S2_minus)
                                                                    (set (min E_S2_minus)))))
                                            (a!19 (and (and true
                                                            (= y_plus 0)
                                                            (> y_minus 0))
                                                       (and (= x_plus 0)
                                                            (> x_minus 0))))
                                            (a!20 (not (and true
                                                            (<= x_minus
                                                                (+ y_minus 1))
                                                            (>= x_minus
                                                                (+ y_minus 1))))))
                                      (let ((a!2 (and a!1
                                                      (subset (set x_plus)
                                                              (setunion (setminus emptyset
                                                                                  emptyset)
                                                                        emptyset))))
                                            (a!3 (and a!1
                                                      (subset (set y_plus)
                                                              (setunion (setminus emptyset
                                                                                  emptyset)
                                                                        emptyset))))
                                            (a!9 (and a!8
                                                      (subset emptyset
                                                              (setunion (setminus emptyset
                                                                                  emptyset)
                                                                        emptyset))))
                                            (a!11 (and true
                                                       (or false
                                                           (and (<= y_plus 0)
                                                                (<= x_minus 1))
                                                           (and (<= y_plus 1)
                                                                (<= x_minus 0)))
                                                       a!10))
                                            (a!16 (and a!15
                                                       (subset emptyset
                                                               (setunion (setminus emptyset
                                                                                   emptyset)
                                                                         emptyset)))))
                                      (let ((a!5 (and a!2
                                                      a!3
                                                      (>= y_plus (+ x_plus 1))
                                                      (forall ((z_plus Int)
                                                               (z_minus Int))
                                                        (let ((a!1 (subset emptyset
                                                                           (setunion (setminus emptyset
                                                                                               E_S2_minus)
                                                                                     (set (min E_S2_minus)))))
                                                              (a!3 (and (>= z_plus
                                                                            (+ x_plus
                                                                               1))
                                                                        (>= y_plus
                                                                            (+ z_plus
                                                                               1))))
                                                              (a!5 (subset (set z_minus)
                                                                           (setunion (setminus emptyset
                                                                                               E_S2_minus)
                                                                                     (set (min E_S2_minus)))))
                                                              (a!7 (or false
                                                                       (and (>= y_plus
                                                                                0)
                                                                            (>= z_minus
                                                                                1))
                                                                       (and (>= y_plus
                                                                                1)
                                                                            (>= z_minus
                                                                                0)))))
                                                        (let ((a!2 (and a!1
                                                                        (subset (set z_plus)
                                                                                (setunion (setminus emptyset
                                                                                                    emptyset)
                                                                                          emptyset))))
                                                              (a!6 (and a!5
                                                                        (subset emptyset
                                                                                (setunion (setminus emptyset
                                                                                                    emptyset)
                                                                                          emptyset)))))
                                                        (let ((a!4 (and (and true
                                                                             (= z_minus
                                                                                0))
                                                                        (not (not (and a!2
                                                                                       a!3)))))
                                                              (a!8 (not (not (and a!6
                                                                                  (and false
                                                                                       a!7))))))
                                                        (let ((a!9 (and (and true
                                                                             (and (= z_plus
                                                                                     0)
                                                                                  (> z_minus
                                                                                     0)))
                                                                        a!8)))
                                                          (and (not a!4)
                                                               (not a!9)))))))
                                                      a!4))
                                            (a!12 (and a!9
                                                       a!3
                                                       a!10
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset emptyset
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!3 (or false
                                                                        (and (>= z_plus
                                                                                 0)
                                                                             (>= x_minus
                                                                                 1))
                                                                        (and (>= z_plus
                                                                                 1)
                                                                             (>= x_minus
                                                                                 0))))
                                                               (a!6 (subset (set z_minus)
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!8 (or false
                                                                        (and (>= y_plus
                                                                                 0)
                                                                             (>= z_minus
                                                                                 1))
                                                                        (and (>= y_plus
                                                                                 1)
                                                                             (>= z_minus
                                                                                 0)))))
                                                         (let ((a!2 (and a!1
                                                                         (subset (set z_plus)
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset))))
                                                               (a!7 (and a!6
                                                                         (subset emptyset
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset)))))
                                                         (let ((a!4 (and a!2
                                                                         (and a!3
                                                                              (>= y_plus
                                                                                  (+ z_plus
                                                                                     1)))))
                                                               (a!9 (and a!7
                                                                         (and (>= x_minus
                                                                                  (+ z_minus
                                                                                     1))
                                                                              a!8))))
                                                         (let ((a!5 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              (not (not a!4)))))
                                                               (a!10 (and (and true
                                                                               (and (= z_plus
                                                                                       0)
                                                                                    (> z_minus
                                                                                       0)))
                                                                          (not (not a!9)))))
                                                           (and a!5 (not a!10)))))))
                                                       (not a!11)))
                                            (a!17 (and a!2
                                                       a!16
                                                       false
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset emptyset
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!5 (subset (set z_minus)
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus))))))
                                                         (let ((a!2 (and a!1
                                                                         (subset (set z_plus)
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset))))
                                                               (a!6 (and a!5
                                                                         (subset emptyset
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset)))))
                                                         (let ((a!3 (and a!2
                                                                         (and (>= z_plus
                                                                                  (+ x_plus
                                                                                     1))
                                                                              false)))
                                                               (a!7 (and a!6
                                                                         (and false
                                                                              (>= z_minus
                                                                                  (+ y_minus
                                                                                     1))))))
                                                         (let ((a!4 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              (not (not a!3)))))
                                                               (a!8 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         (not (not a!7)))))
                                                           (and a!4 (not a!8)))))))
                                                       (not (and true
                                                                 true
                                                                 false))))
                                            (a!21 (and a!9
                                                       a!16
                                                       (>= x_minus
                                                           (+ y_minus 1))
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset emptyset
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!3 (or false
                                                                        (and (>= z_plus
                                                                                 0)
                                                                             (>= x_minus
                                                                                 1))
                                                                        (and (>= z_plus
                                                                                 1)
                                                                             (>= x_minus
                                                                                 0))))
                                                               (a!6 (subset (set z_minus)
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_minus)
                                                                                      (set (min E_S2_minus)))))
                                                               (a!8 (and (>= x_minus
                                                                             (+ z_minus
                                                                                1))
                                                                         (>= z_minus
                                                                             (+ y_minus
                                                                                1)))))
                                                         (let ((a!2 (and a!1
                                                                         (subset (set z_plus)
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset))))
                                                               (a!7 (and a!6
                                                                         (subset emptyset
                                                                                 (setunion (setminus emptyset
                                                                                                     emptyset)
                                                                                           emptyset)))))
                                                         (let ((a!4 (not (not (and a!2
                                                                                   (and a!3
                                                                                        false)))))
                                                               (a!9 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         (not (not (and a!7
                                                                                        a!8))))))
                                                         (let ((a!5 (not (and (and true
                                                                                   (= z_minus
                                                                                      0))
                                                                              a!4))))
                                                           (and a!5 (not a!9)))))))
                                                       a!20)))
                                      (let ((a!6 (and (and (and true
                                                                (= y_minus 0))
                                                           (= x_minus 0))
                                                      (not (not a!5))))
                                            (a!13 (not (and a!7
                                                            (not (not a!12)))))
                                            (a!18 (not (and a!14
                                                            (not (not a!17)))))
                                            (a!22 (not (and a!19
                                                            (not (not a!21))))))
                                        (and (not a!6) a!13 a!18 a!22))))))))
                         (a!109 (and (and (= S1_2_minus
                                             (setunion emptyset emptyset))
                                          a!1)
                                     (and (= E_S2_minus
                                             (setunion S2_minus emptyset))
                                          a!2)
                                     (subset E_S2_minus emptyset)
                                     (subset E_S2_plus E_S1_plus)
                                     (not (and (= S2_minus emptyset)
                                               (= S2_plus emptyset)))
                                     (not (and a!101 (not a!102)))
                                     (and true a!8 a!11)
                                     (and true a!104 (or a!16 a!105))
                                     (and true a!21)
                                     (and true a!108)
                                     (and true a!28)
                                     a!32
                                     (forall ((y_plus Int)
                                              (y_minus Int)
                                              (x_plus Int)
                                              (x_minus Int))
                                       (let ((a!1 (subset (set x_plus)
                                                          (setunion (setminus E_S1_plus
                                                                              E_S2_plus)
                                                                    (set (max E_S2_plus)))))
                                             (a!3 (subset (set y_plus)
                                                          (setunion (setminus E_S1_plus
                                                                              E_S2_plus)
                                                                    (set (max E_S2_plus)))))
                                             (a!5 (not (and true
                                                            (<= y_plus
                                                                (+ x_plus 1))
                                                            (>= y_plus
                                                                (+ x_plus 1)))))
                                             (a!8 (and (and true (= y_minus 0))
                                                       (and (= x_plus 0)
                                                            (> x_minus 0))))
                                             (a!9 (subset emptyset
                                                          (setunion (setminus E_S1_plus
                                                                              E_S2_plus)
                                                                    (set (max E_S2_plus)))))
                                             (a!11 (or false
                                                       (and (>= y_plus 0)
                                                            (>= x_minus 1))
                                                       (and (>= y_plus 1)
                                                            (>= x_minus 0))))
                                             (a!15 (and (and true
                                                             (= y_plus 0)
                                                             (> y_minus 0))
                                                        (= x_minus 0)))
                                             (a!19 (and (and true
                                                             (= y_plus 0)
                                                             (> y_minus 0))
                                                        (and (= x_plus 0)
                                                             (> x_minus 0))))
                                             (a!20 (not (and true
                                                             (<= x_minus
                                                                 (+ y_minus 1))
                                                             (>= x_minus
                                                                 (+ y_minus 1))))))
                                       (let ((a!2 (and (subset emptyset
                                                               (setunion (setminus emptyset
                                                                                   E_S2_minus)
                                                                         emptyset))
                                                       a!1))
                                             (a!4 (and (subset emptyset
                                                               (setunion (setminus emptyset
                                                                                   E_S2_minus)
                                                                         emptyset))
                                                       a!3))
                                             (a!10 (and (subset (set x_minus)
                                                                (setunion (setminus emptyset
                                                                                    E_S2_minus)
                                                                          emptyset))
                                                        a!9))
                                             (a!12 (and true
                                                        (or false
                                                            (and (<= y_plus 0)
                                                                 (<= x_minus 1))
                                                            (and (<= y_plus 1)
                                                                 (<= x_minus 0)))
                                                        a!11))
                                             (a!16 (and (subset (set y_minus)
                                                                (setunion (setminus emptyset
                                                                                    E_S2_minus)
                                                                          emptyset))
                                                        a!9)))
                                       (let ((a!6 (and a!2
                                                       a!4
                                                       (>= y_plus (+ x_plus 1))
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset (set z_plus)
                                                                            (setunion (setminus E_S1_plus
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!3 (and (>= z_plus
                                                                             (+ x_plus
                                                                                1))
                                                                         (>= y_plus
                                                                             (+ z_plus
                                                                                1))))
                                                               (a!5 (subset emptyset
                                                                            (setunion (setminus E_S1_plus
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!7 (or false
                                                                        (and (>= y_plus
                                                                                 0)
                                                                             (>= z_minus
                                                                                 1))
                                                                        (and (>= y_plus
                                                                                 1)
                                                                             (>= z_minus
                                                                                 0)))))
                                                         (let ((a!2 (and (subset emptyset
                                                                                 (setunion (setminus emptyset
                                                                                                     E_S2_minus)
                                                                                           emptyset))
                                                                         a!1))
                                                               (a!6 (and (subset (set z_minus)
                                                                                 (setunion (setminus emptyset
                                                                                                     E_S2_minus)
                                                                                           emptyset))
                                                                         a!5)))
                                                         (let ((a!4 (and (and true
                                                                              (= z_minus
                                                                                 0))
                                                                         (not (not (and a!2
                                                                                        a!3)))))
                                                               (a!8 (not (not (and a!6
                                                                                   (and false
                                                                                        a!7))))))
                                                         (let ((a!9 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         a!8)))
                                                           (and (not a!4)
                                                                (not a!9)))))))
                                                       a!5))
                                             (a!13 (and a!10
                                                        a!4
                                                        a!11
                                                        (forall ((z_plus Int)
                                                                 (z_minus Int))
                                                          (let ((a!1 (subset (set z_plus)
                                                                             (setunion (setminus E_S1_plus
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!3 (or false
                                                                         (and (>= z_plus
                                                                                  0)
                                                                              (>= x_minus
                                                                                  1))
                                                                         (and (>= z_plus
                                                                                  1)
                                                                              (>= x_minus
                                                                                  0))))
                                                                (a!6 (subset emptyset
                                                                             (setunion (setminus E_S1_plus
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!8 (or false
                                                                         (and (>= y_plus
                                                                                  0)
                                                                              (>= z_minus
                                                                                  1))
                                                                         (and (>= y_plus
                                                                                  1)
                                                                              (>= z_minus
                                                                                  0)))))
                                                          (let ((a!2 (and (subset emptyset
                                                                                  (setunion (setminus emptyset
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!1))
                                                                (a!7 (and (subset (set z_minus)
                                                                                  (setunion (setminus emptyset
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!6)))
                                                          (let ((a!4 (and a!2
                                                                          (and a!3
                                                                               (>= y_plus
                                                                                   (+ z_plus
                                                                                      1)))))
                                                                (a!9 (and a!7
                                                                          (and (>= x_minus
                                                                                   (+ z_minus
                                                                                      1))
                                                                               a!8))))
                                                          (let ((a!5 (not (and (and true
                                                                                    (= z_minus
                                                                                       0))
                                                                               (not (not a!4)))))
                                                                (a!10 (and (and true
                                                                                (and (= z_plus
                                                                                        0)
                                                                                     (> z_minus
                                                                                        0)))
                                                                           (not (not a!9)))))
                                                            (and a!5 (not a!10)))))))
                                                        (not a!12)))
                                             (a!17 (and a!2
                                                        a!16
                                                        false
                                                        (forall ((z_plus Int)
                                                                 (z_minus Int))
                                                          (let ((a!1 (subset (set z_plus)
                                                                             (setunion (setminus E_S1_plus
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!5 (subset emptyset
                                                                             (setunion (setminus E_S1_plus
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus))))))
                                                          (let ((a!2 (and (subset emptyset
                                                                                  (setunion (setminus emptyset
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!1))
                                                                (a!6 (and (subset (set z_minus)
                                                                                  (setunion (setminus emptyset
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!5)))
                                                          (let ((a!3 (and a!2
                                                                          (and (>= z_plus
                                                                                   (+ x_plus
                                                                                      1))
                                                                               false)))
                                                                (a!7 (and a!6
                                                                          (and false
                                                                               (>= z_minus
                                                                                   (+ y_minus
                                                                                      1))))))
                                                          (let ((a!4 (not (and (and true
                                                                                    (= z_minus
                                                                                       0))
                                                                               (not (not a!3)))))
                                                                (a!8 (and (and true
                                                                               (and (= z_plus
                                                                                       0)
                                                                                    (> z_minus
                                                                                       0)))
                                                                          (not (not a!7)))))
                                                            (and a!4 (not a!8)))))))
                                                        (not (and true
                                                                  true
                                                                  false))))
                                             (a!21 (and a!10
                                                        a!16
                                                        (>= x_minus
                                                            (+ y_minus 1))
                                                        (forall ((z_plus Int)
                                                                 (z_minus Int))
                                                          (let ((a!1 (subset (set z_plus)
                                                                             (setunion (setminus E_S1_plus
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!3 (or false
                                                                         (and (>= z_plus
                                                                                  0)
                                                                              (>= x_minus
                                                                                  1))
                                                                         (and (>= z_plus
                                                                                  1)
                                                                              (>= x_minus
                                                                                  0))))
                                                                (a!6 (subset emptyset
                                                                             (setunion (setminus E_S1_plus
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!8 (and (>= x_minus
                                                                              (+ z_minus
                                                                                 1))
                                                                          (>= z_minus
                                                                              (+ y_minus
                                                                                 1)))))
                                                          (let ((a!2 (and (subset emptyset
                                                                                  (setunion (setminus emptyset
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!1))
                                                                (a!7 (and (subset (set z_minus)
                                                                                  (setunion (setminus emptyset
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!6)))
                                                          (let ((a!4 (not (not (and a!2
                                                                                    (and a!3
                                                                                         false)))))
                                                                (a!9 (and (and true
                                                                               (and (= z_plus
                                                                                       0)
                                                                                    (> z_minus
                                                                                       0)))
                                                                          (not (not (and a!7
                                                                                         a!8))))))
                                                          (let ((a!5 (not (and (and true
                                                                                    (= z_minus
                                                                                       0))
                                                                               a!4))))
                                                            (and a!5 (not a!9)))))))
                                                        a!20)))
                                       (let ((a!7 (and (and (and true
                                                                 (= y_minus 0))
                                                            (= x_minus 0))
                                                       (not (not a!6))))
                                             (a!14 (not (and a!8
                                                             (not (not a!13)))))
                                             (a!18 (not (and a!15
                                                             (not (not a!17)))))
                                             (a!22 (not (and a!19
                                                             (not (not a!21))))))
                                         (and (not a!7) a!14 a!18 a!22))))))))
                         (a!113 (and (and (= S1_2_minus
                                             (setunion E_S1_minus emptyset))
                                          a!35)
                                     (and (= E_S2_minus
                                             (setunion S2_minus emptyset))
                                          a!2)
                                     (subset E_S2_minus E_S1_minus)
                                     (subset E_S2_plus emptyset)
                                     (not (and (= S2_minus emptyset)
                                               (= S2_plus emptyset)))
                                     (not (and a!111 (not a!112)))
                                     (and true a!41 a!44)
                                     (and true a!104 (or a!16 a!105))
                                     (and true a!21)
                                     (and true a!108)
                                     (and true a!28)
                                     (and true a!48)
                                     (forall ((y_plus Int)
                                              (y_minus Int)
                                              (x_plus Int)
                                              (x_minus Int))
                                       (let ((a!1 (subset (set x_plus)
                                                          (setunion (setminus emptyset
                                                                              E_S2_plus)
                                                                    (set (max E_S2_plus)))))
                                             (a!3 (subset (set y_plus)
                                                          (setunion (setminus emptyset
                                                                              E_S2_plus)
                                                                    (set (max E_S2_plus)))))
                                             (a!5 (not (and true
                                                            (<= y_plus
                                                                (+ x_plus 1))
                                                            (>= y_plus
                                                                (+ x_plus 1)))))
                                             (a!8 (and (and true (= y_minus 0))
                                                       (and (= x_plus 0)
                                                            (> x_minus 0))))
                                             (a!9 (subset emptyset
                                                          (setunion (setminus emptyset
                                                                              E_S2_plus)
                                                                    (set (max E_S2_plus)))))
                                             (a!11 (or false
                                                       (and (>= y_plus 0)
                                                            (>= x_minus 1))
                                                       (and (>= y_plus 1)
                                                            (>= x_minus 0))))
                                             (a!15 (and (and true
                                                             (= y_plus 0)
                                                             (> y_minus 0))
                                                        (= x_minus 0)))
                                             (a!19 (and (and true
                                                             (= y_plus 0)
                                                             (> y_minus 0))
                                                        (and (= x_plus 0)
                                                             (> x_minus 0))))
                                             (a!20 (not (and true
                                                             (<= x_minus
                                                                 (+ y_minus 1))
                                                             (>= x_minus
                                                                 (+ y_minus 1))))))
                                       (let ((a!2 (and (subset emptyset
                                                               (setunion (setminus E_S1_minus
                                                                                   E_S2_minus)
                                                                         emptyset))
                                                       a!1))
                                             (a!4 (and (subset emptyset
                                                               (setunion (setminus E_S1_minus
                                                                                   E_S2_minus)
                                                                         emptyset))
                                                       a!3))
                                             (a!10 (and (subset (set x_minus)
                                                                (setunion (setminus E_S1_minus
                                                                                    E_S2_minus)
                                                                          emptyset))
                                                        a!9))
                                             (a!12 (and true
                                                        (or false
                                                            (and (<= y_plus 0)
                                                                 (<= x_minus 1))
                                                            (and (<= y_plus 1)
                                                                 (<= x_minus 0)))
                                                        a!11))
                                             (a!16 (and (subset (set y_minus)
                                                                (setunion (setminus E_S1_minus
                                                                                    E_S2_minus)
                                                                          emptyset))
                                                        a!9)))
                                       (let ((a!6 (and a!2
                                                       a!4
                                                       (>= y_plus (+ x_plus 1))
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset (set z_plus)
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!3 (and (>= z_plus
                                                                             (+ x_plus
                                                                                1))
                                                                         (>= y_plus
                                                                             (+ z_plus
                                                                                1))))
                                                               (a!5 (subset emptyset
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!7 (or false
                                                                        (and (>= y_plus
                                                                                 0)
                                                                             (>= z_minus
                                                                                 1))
                                                                        (and (>= y_plus
                                                                                 1)
                                                                             (>= z_minus
                                                                                 0)))))
                                                         (let ((a!2 (and (subset emptyset
                                                                                 (setunion (setminus E_S1_minus
                                                                                                     E_S2_minus)
                                                                                           emptyset))
                                                                         a!1))
                                                               (a!6 (and (subset (set z_minus)
                                                                                 (setunion (setminus E_S1_minus
                                                                                                     E_S2_minus)
                                                                                           emptyset))
                                                                         a!5)))
                                                         (let ((a!4 (and (and true
                                                                              (= z_minus
                                                                                 0))
                                                                         (not (not (and a!2
                                                                                        a!3)))))
                                                               (a!8 (not (not (and a!6
                                                                                   (and false
                                                                                        a!7))))))
                                                         (let ((a!9 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         a!8)))
                                                           (and (not a!4)
                                                                (not a!9)))))))
                                                       a!5))
                                             (a!13 (and a!10
                                                        a!4
                                                        a!11
                                                        (forall ((z_plus Int)
                                                                 (z_minus Int))
                                                          (let ((a!1 (subset (set z_plus)
                                                                             (setunion (setminus emptyset
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!3 (or false
                                                                         (and (>= z_plus
                                                                                  0)
                                                                              (>= x_minus
                                                                                  1))
                                                                         (and (>= z_plus
                                                                                  1)
                                                                              (>= x_minus
                                                                                  0))))
                                                                (a!6 (subset emptyset
                                                                             (setunion (setminus emptyset
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!8 (or false
                                                                         (and (>= y_plus
                                                                                  0)
                                                                              (>= z_minus
                                                                                  1))
                                                                         (and (>= y_plus
                                                                                  1)
                                                                              (>= z_minus
                                                                                  0)))))
                                                          (let ((a!2 (and (subset emptyset
                                                                                  (setunion (setminus E_S1_minus
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!1))
                                                                (a!7 (and (subset (set z_minus)
                                                                                  (setunion (setminus E_S1_minus
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!6)))
                                                          (let ((a!4 (and a!2
                                                                          (and a!3
                                                                               (>= y_plus
                                                                                   (+ z_plus
                                                                                      1)))))
                                                                (a!9 (and a!7
                                                                          (and (>= x_minus
                                                                                   (+ z_minus
                                                                                      1))
                                                                               a!8))))
                                                          (let ((a!5 (not (and (and true
                                                                                    (= z_minus
                                                                                       0))
                                                                               (not (not a!4)))))
                                                                (a!10 (and (and true
                                                                                (and (= z_plus
                                                                                        0)
                                                                                     (> z_minus
                                                                                        0)))
                                                                           (not (not a!9)))))
                                                            (and a!5 (not a!10)))))))
                                                        (not a!12)))
                                             (a!17 (and a!2
                                                        a!16
                                                        false
                                                        (forall ((z_plus Int)
                                                                 (z_minus Int))
                                                          (let ((a!1 (subset (set z_plus)
                                                                             (setunion (setminus emptyset
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!5 (subset emptyset
                                                                             (setunion (setminus emptyset
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus))))))
                                                          (let ((a!2 (and (subset emptyset
                                                                                  (setunion (setminus E_S1_minus
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!1))
                                                                (a!6 (and (subset (set z_minus)
                                                                                  (setunion (setminus E_S1_minus
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!5)))
                                                          (let ((a!3 (and a!2
                                                                          (and (>= z_plus
                                                                                   (+ x_plus
                                                                                      1))
                                                                               false)))
                                                                (a!7 (and a!6
                                                                          (and false
                                                                               (>= z_minus
                                                                                   (+ y_minus
                                                                                      1))))))
                                                          (let ((a!4 (not (and (and true
                                                                                    (= z_minus
                                                                                       0))
                                                                               (not (not a!3)))))
                                                                (a!8 (and (and true
                                                                               (and (= z_plus
                                                                                       0)
                                                                                    (> z_minus
                                                                                       0)))
                                                                          (not (not a!7)))))
                                                            (and a!4 (not a!8)))))))
                                                        (not (and true
                                                                  true
                                                                  false))))
                                             (a!21 (and a!10
                                                        a!16
                                                        (>= x_minus
                                                            (+ y_minus 1))
                                                        (forall ((z_plus Int)
                                                                 (z_minus Int))
                                                          (let ((a!1 (subset (set z_plus)
                                                                             (setunion (setminus emptyset
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!3 (or false
                                                                         (and (>= z_plus
                                                                                  0)
                                                                              (>= x_minus
                                                                                  1))
                                                                         (and (>= z_plus
                                                                                  1)
                                                                              (>= x_minus
                                                                                  0))))
                                                                (a!6 (subset emptyset
                                                                             (setunion (setminus emptyset
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!8 (and (>= x_minus
                                                                              (+ z_minus
                                                                                 1))
                                                                          (>= z_minus
                                                                              (+ y_minus
                                                                                 1)))))
                                                          (let ((a!2 (and (subset emptyset
                                                                                  (setunion (setminus E_S1_minus
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!1))
                                                                (a!7 (and (subset (set z_minus)
                                                                                  (setunion (setminus E_S1_minus
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!6)))
                                                          (let ((a!4 (not (not (and a!2
                                                                                    (and a!3
                                                                                         false)))))
                                                                (a!9 (and (and true
                                                                               (and (= z_plus
                                                                                       0)
                                                                                    (> z_minus
                                                                                       0)))
                                                                          (not (not (and a!7
                                                                                         a!8))))))
                                                          (let ((a!5 (not (and (and true
                                                                                    (= z_minus
                                                                                       0))
                                                                               a!4))))
                                                            (and a!5 (not a!9)))))))
                                                        a!20)))
                                       (let ((a!7 (and (and (and true
                                                                 (= y_minus 0))
                                                            (= x_minus 0))
                                                       (not (not a!6))))
                                             (a!14 (not (and a!8
                                                             (not (not a!13)))))
                                             (a!18 (not (and a!15
                                                             (not (not a!17)))))
                                             (a!22 (not (and a!19
                                                             (not (not a!21))))))
                                         (and (not a!7) a!14 a!18 a!22))))))))
                         (a!117 (and (and (= S1_2_minus
                                             (setunion E_S1_minus emptyset))
                                          a!1)
                                     (and (= E_S2_minus
                                             (setunion S2_minus emptyset))
                                          a!2)
                                     (subset E_S2_minus E_S1_minus)
                                     (subset E_S2_plus E_S1_plus)
                                     (not (and (= S2_minus emptyset)
                                               (= S2_plus emptyset)))
                                     (not (and a!115 (not a!116)))
                                     (and true a!54 a!56)
                                     (and true a!104 (or a!16 a!105))
                                     (and true a!21)
                                     (and true a!108)
                                     (and true a!28)
                                     a!60
                                     (forall ((y_plus Int)
                                              (y_minus Int)
                                              (x_plus Int)
                                              (x_minus Int))
                                       (let ((a!1 (subset (set x_plus)
                                                          (setunion (setminus E_S1_plus
                                                                              E_S2_plus)
                                                                    (set (max E_S2_plus)))))
                                             (a!3 (subset (set y_plus)
                                                          (setunion (setminus E_S1_plus
                                                                              E_S2_plus)
                                                                    (set (max E_S2_plus)))))
                                             (a!5 (not (and true
                                                            (<= y_plus
                                                                (+ x_plus 1))
                                                            (>= y_plus
                                                                (+ x_plus 1)))))
                                             (a!8 (and (and true (= y_minus 0))
                                                       (and (= x_plus 0)
                                                            (> x_minus 0))))
                                             (a!9 (subset emptyset
                                                          (setunion (setminus E_S1_plus
                                                                              E_S2_plus)
                                                                    (set (max E_S2_plus)))))
                                             (a!11 (or false
                                                       (and (>= y_plus 0)
                                                            (>= x_minus 1))
                                                       (and (>= y_plus 1)
                                                            (>= x_minus 0))))
                                             (a!15 (and (and true
                                                             (= y_plus 0)
                                                             (> y_minus 0))
                                                        (= x_minus 0)))
                                             (a!19 (and (and true
                                                             (= y_plus 0)
                                                             (> y_minus 0))
                                                        (and (= x_plus 0)
                                                             (> x_minus 0))))
                                             (a!20 (not (and true
                                                             (<= x_minus
                                                                 (+ y_minus 1))
                                                             (>= x_minus
                                                                 (+ y_minus 1))))))
                                       (let ((a!2 (and (subset emptyset
                                                               (setunion (setminus E_S1_minus
                                                                                   E_S2_minus)
                                                                         emptyset))
                                                       a!1))
                                             (a!4 (and (subset emptyset
                                                               (setunion (setminus E_S1_minus
                                                                                   E_S2_minus)
                                                                         emptyset))
                                                       a!3))
                                             (a!10 (and (subset (set x_minus)
                                                                (setunion (setminus E_S1_minus
                                                                                    E_S2_minus)
                                                                          emptyset))
                                                        a!9))
                                             (a!12 (and true
                                                        (or false
                                                            (and (<= y_plus 0)
                                                                 (<= x_minus 1))
                                                            (and (<= y_plus 1)
                                                                 (<= x_minus 0)))
                                                        a!11))
                                             (a!16 (and (subset (set y_minus)
                                                                (setunion (setminus E_S1_minus
                                                                                    E_S2_minus)
                                                                          emptyset))
                                                        a!9)))
                                       (let ((a!6 (and a!2
                                                       a!4
                                                       (>= y_plus (+ x_plus 1))
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset (set z_plus)
                                                                            (setunion (setminus E_S1_plus
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!3 (and (>= z_plus
                                                                             (+ x_plus
                                                                                1))
                                                                         (>= y_plus
                                                                             (+ z_plus
                                                                                1))))
                                                               (a!5 (subset emptyset
                                                                            (setunion (setminus E_S1_plus
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!7 (or false
                                                                        (and (>= y_plus
                                                                                 0)
                                                                             (>= z_minus
                                                                                 1))
                                                                        (and (>= y_plus
                                                                                 1)
                                                                             (>= z_minus
                                                                                 0)))))
                                                         (let ((a!2 (and (subset emptyset
                                                                                 (setunion (setminus E_S1_minus
                                                                                                     E_S2_minus)
                                                                                           emptyset))
                                                                         a!1))
                                                               (a!6 (and (subset (set z_minus)
                                                                                 (setunion (setminus E_S1_minus
                                                                                                     E_S2_minus)
                                                                                           emptyset))
                                                                         a!5)))
                                                         (let ((a!4 (and (and true
                                                                              (= z_minus
                                                                                 0))
                                                                         (not (not (and a!2
                                                                                        a!3)))))
                                                               (a!8 (not (not (and a!6
                                                                                   (and false
                                                                                        a!7))))))
                                                         (let ((a!9 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         a!8)))
                                                           (and (not a!4)
                                                                (not a!9)))))))
                                                       a!5))
                                             (a!13 (and a!10
                                                        a!4
                                                        a!11
                                                        (forall ((z_plus Int)
                                                                 (z_minus Int))
                                                          (let ((a!1 (subset (set z_plus)
                                                                             (setunion (setminus E_S1_plus
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!3 (or false
                                                                         (and (>= z_plus
                                                                                  0)
                                                                              (>= x_minus
                                                                                  1))
                                                                         (and (>= z_plus
                                                                                  1)
                                                                              (>= x_minus
                                                                                  0))))
                                                                (a!6 (subset emptyset
                                                                             (setunion (setminus E_S1_plus
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!8 (or false
                                                                         (and (>= y_plus
                                                                                  0)
                                                                              (>= z_minus
                                                                                  1))
                                                                         (and (>= y_plus
                                                                                  1)
                                                                              (>= z_minus
                                                                                  0)))))
                                                          (let ((a!2 (and (subset emptyset
                                                                                  (setunion (setminus E_S1_minus
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!1))
                                                                (a!7 (and (subset (set z_minus)
                                                                                  (setunion (setminus E_S1_minus
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!6)))
                                                          (let ((a!4 (and a!2
                                                                          (and a!3
                                                                               (>= y_plus
                                                                                   (+ z_plus
                                                                                      1)))))
                                                                (a!9 (and a!7
                                                                          (and (>= x_minus
                                                                                   (+ z_minus
                                                                                      1))
                                                                               a!8))))
                                                          (let ((a!5 (not (and (and true
                                                                                    (= z_minus
                                                                                       0))
                                                                               (not (not a!4)))))
                                                                (a!10 (and (and true
                                                                                (and (= z_plus
                                                                                        0)
                                                                                     (> z_minus
                                                                                        0)))
                                                                           (not (not a!9)))))
                                                            (and a!5 (not a!10)))))))
                                                        (not a!12)))
                                             (a!17 (and a!2
                                                        a!16
                                                        false
                                                        (forall ((z_plus Int)
                                                                 (z_minus Int))
                                                          (let ((a!1 (subset (set z_plus)
                                                                             (setunion (setminus E_S1_plus
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!5 (subset emptyset
                                                                             (setunion (setminus E_S1_plus
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus))))))
                                                          (let ((a!2 (and (subset emptyset
                                                                                  (setunion (setminus E_S1_minus
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!1))
                                                                (a!6 (and (subset (set z_minus)
                                                                                  (setunion (setminus E_S1_minus
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!5)))
                                                          (let ((a!3 (and a!2
                                                                          (and (>= z_plus
                                                                                   (+ x_plus
                                                                                      1))
                                                                               false)))
                                                                (a!7 (and a!6
                                                                          (and false
                                                                               (>= z_minus
                                                                                   (+ y_minus
                                                                                      1))))))
                                                          (let ((a!4 (not (and (and true
                                                                                    (= z_minus
                                                                                       0))
                                                                               (not (not a!3)))))
                                                                (a!8 (and (and true
                                                                               (and (= z_plus
                                                                                       0)
                                                                                    (> z_minus
                                                                                       0)))
                                                                          (not (not a!7)))))
                                                            (and a!4 (not a!8)))))))
                                                        (not (and true
                                                                  true
                                                                  false))))
                                             (a!21 (and a!10
                                                        a!16
                                                        (>= x_minus
                                                            (+ y_minus 1))
                                                        (forall ((z_plus Int)
                                                                 (z_minus Int))
                                                          (let ((a!1 (subset (set z_plus)
                                                                             (setunion (setminus E_S1_plus
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!3 (or false
                                                                         (and (>= z_plus
                                                                                  0)
                                                                              (>= x_minus
                                                                                  1))
                                                                         (and (>= z_plus
                                                                                  1)
                                                                              (>= x_minus
                                                                                  0))))
                                                                (a!6 (subset emptyset
                                                                             (setunion (setminus E_S1_plus
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!8 (and (>= x_minus
                                                                              (+ z_minus
                                                                                 1))
                                                                          (>= z_minus
                                                                              (+ y_minus
                                                                                 1)))))
                                                          (let ((a!2 (and (subset emptyset
                                                                                  (setunion (setminus E_S1_minus
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!1))
                                                                (a!7 (and (subset (set z_minus)
                                                                                  (setunion (setminus E_S1_minus
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!6)))
                                                          (let ((a!4 (not (not (and a!2
                                                                                    (and a!3
                                                                                         false)))))
                                                                (a!9 (and (and true
                                                                               (and (= z_plus
                                                                                       0)
                                                                                    (> z_minus
                                                                                       0)))
                                                                          (not (not (and a!7
                                                                                         a!8))))))
                                                          (let ((a!5 (not (and (and true
                                                                                    (= z_minus
                                                                                       0))
                                                                               a!4))))
                                                            (and a!5 (not a!9)))))))
                                                        a!20)))
                                       (let ((a!7 (and (and (and true
                                                                 (= y_minus 0))
                                                            (= x_minus 0))
                                                       (not (not a!6))))
                                             (a!14 (not (and a!8
                                                             (not (not a!13)))))
                                             (a!18 (not (and a!15
                                                             (not (not a!17)))))
                                             (a!22 (not (and a!19
                                                             (not (not a!21))))))
                                         (and (not a!7) a!14 a!18 a!22))))))))
                         (a!121 (and (and (= S1_2_minus
                                             (setunion emptyset emptyset))
                                          a!35)
                                     (and (= E_S2_minus
                                             (setunion S2_minus emptyset))
                                          a!2)
                                     (subset E_S2_minus emptyset)
                                     (subset E_S2_plus emptyset)
                                     (not (and (= S2_minus emptyset)
                                               (= S2_plus emptyset)))
                                     (not (and a!119 (not a!120)))
                                     (and true a!66 a!68)
                                     (and true a!104 (or a!16 a!105))
                                     (and true a!21)
                                     (and true a!108)
                                     (and true a!28)
                                     (and true a!71)
                                     (forall ((y_plus Int)
                                              (y_minus Int)
                                              (x_plus Int)
                                              (x_minus Int))
                                       (let ((a!1 (subset (set x_plus)
                                                          (setunion (setminus emptyset
                                                                              E_S2_plus)
                                                                    (set (max E_S2_plus)))))
                                             (a!3 (subset (set y_plus)
                                                          (setunion (setminus emptyset
                                                                              E_S2_plus)
                                                                    (set (max E_S2_plus)))))
                                             (a!5 (not (and true
                                                            (<= y_plus
                                                                (+ x_plus 1))
                                                            (>= y_plus
                                                                (+ x_plus 1)))))
                                             (a!8 (and (and true (= y_minus 0))
                                                       (and (= x_plus 0)
                                                            (> x_minus 0))))
                                             (a!9 (subset emptyset
                                                          (setunion (setminus emptyset
                                                                              E_S2_plus)
                                                                    (set (max E_S2_plus)))))
                                             (a!11 (or false
                                                       (and (>= y_plus 0)
                                                            (>= x_minus 1))
                                                       (and (>= y_plus 1)
                                                            (>= x_minus 0))))
                                             (a!15 (and (and true
                                                             (= y_plus 0)
                                                             (> y_minus 0))
                                                        (= x_minus 0)))
                                             (a!19 (and (and true
                                                             (= y_plus 0)
                                                             (> y_minus 0))
                                                        (and (= x_plus 0)
                                                             (> x_minus 0))))
                                             (a!20 (not (and true
                                                             (<= x_minus
                                                                 (+ y_minus 1))
                                                             (>= x_minus
                                                                 (+ y_minus 1))))))
                                       (let ((a!2 (and (subset emptyset
                                                               (setunion (setminus emptyset
                                                                                   E_S2_minus)
                                                                         emptyset))
                                                       a!1))
                                             (a!4 (and (subset emptyset
                                                               (setunion (setminus emptyset
                                                                                   E_S2_minus)
                                                                         emptyset))
                                                       a!3))
                                             (a!10 (and (subset (set x_minus)
                                                                (setunion (setminus emptyset
                                                                                    E_S2_minus)
                                                                          emptyset))
                                                        a!9))
                                             (a!12 (and true
                                                        (or false
                                                            (and (<= y_plus 0)
                                                                 (<= x_minus 1))
                                                            (and (<= y_plus 1)
                                                                 (<= x_minus 0)))
                                                        a!11))
                                             (a!16 (and (subset (set y_minus)
                                                                (setunion (setminus emptyset
                                                                                    E_S2_minus)
                                                                          emptyset))
                                                        a!9)))
                                       (let ((a!6 (and a!2
                                                       a!4
                                                       (>= y_plus (+ x_plus 1))
                                                       (forall ((z_plus Int)
                                                                (z_minus Int))
                                                         (let ((a!1 (subset (set z_plus)
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!3 (and (>= z_plus
                                                                             (+ x_plus
                                                                                1))
                                                                         (>= y_plus
                                                                             (+ z_plus
                                                                                1))))
                                                               (a!5 (subset emptyset
                                                                            (setunion (setminus emptyset
                                                                                                E_S2_plus)
                                                                                      (set (max E_S2_plus)))))
                                                               (a!7 (or false
                                                                        (and (>= y_plus
                                                                                 0)
                                                                             (>= z_minus
                                                                                 1))
                                                                        (and (>= y_plus
                                                                                 1)
                                                                             (>= z_minus
                                                                                 0)))))
                                                         (let ((a!2 (and (subset emptyset
                                                                                 (setunion (setminus emptyset
                                                                                                     E_S2_minus)
                                                                                           emptyset))
                                                                         a!1))
                                                               (a!6 (and (subset (set z_minus)
                                                                                 (setunion (setminus emptyset
                                                                                                     E_S2_minus)
                                                                                           emptyset))
                                                                         a!5)))
                                                         (let ((a!4 (and (and true
                                                                              (= z_minus
                                                                                 0))
                                                                         (not (not (and a!2
                                                                                        a!3)))))
                                                               (a!8 (not (not (and a!6
                                                                                   (and false
                                                                                        a!7))))))
                                                         (let ((a!9 (and (and true
                                                                              (and (= z_plus
                                                                                      0)
                                                                                   (> z_minus
                                                                                      0)))
                                                                         a!8)))
                                                           (and (not a!4)
                                                                (not a!9)))))))
                                                       a!5))
                                             (a!13 (and a!10
                                                        a!4
                                                        a!11
                                                        (forall ((z_plus Int)
                                                                 (z_minus Int))
                                                          (let ((a!1 (subset (set z_plus)
                                                                             (setunion (setminus emptyset
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!3 (or false
                                                                         (and (>= z_plus
                                                                                  0)
                                                                              (>= x_minus
                                                                                  1))
                                                                         (and (>= z_plus
                                                                                  1)
                                                                              (>= x_minus
                                                                                  0))))
                                                                (a!6 (subset emptyset
                                                                             (setunion (setminus emptyset
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!8 (or false
                                                                         (and (>= y_plus
                                                                                  0)
                                                                              (>= z_minus
                                                                                  1))
                                                                         (and (>= y_plus
                                                                                  1)
                                                                              (>= z_minus
                                                                                  0)))))
                                                          (let ((a!2 (and (subset emptyset
                                                                                  (setunion (setminus emptyset
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!1))
                                                                (a!7 (and (subset (set z_minus)
                                                                                  (setunion (setminus emptyset
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!6)))
                                                          (let ((a!4 (and a!2
                                                                          (and a!3
                                                                               (>= y_plus
                                                                                   (+ z_plus
                                                                                      1)))))
                                                                (a!9 (and a!7
                                                                          (and (>= x_minus
                                                                                   (+ z_minus
                                                                                      1))
                                                                               a!8))))
                                                          (let ((a!5 (not (and (and true
                                                                                    (= z_minus
                                                                                       0))
                                                                               (not (not a!4)))))
                                                                (a!10 (and (and true
                                                                                (and (= z_plus
                                                                                        0)
                                                                                     (> z_minus
                                                                                        0)))
                                                                           (not (not a!9)))))
                                                            (and a!5 (not a!10)))))))
                                                        (not a!12)))
                                             (a!17 (and a!2
                                                        a!16
                                                        false
                                                        (forall ((z_plus Int)
                                                                 (z_minus Int))
                                                          (let ((a!1 (subset (set z_plus)
                                                                             (setunion (setminus emptyset
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!5 (subset emptyset
                                                                             (setunion (setminus emptyset
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus))))))
                                                          (let ((a!2 (and (subset emptyset
                                                                                  (setunion (setminus emptyset
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!1))
                                                                (a!6 (and (subset (set z_minus)
                                                                                  (setunion (setminus emptyset
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!5)))
                                                          (let ((a!3 (and a!2
                                                                          (and (>= z_plus
                                                                                   (+ x_plus
                                                                                      1))
                                                                               false)))
                                                                (a!7 (and a!6
                                                                          (and false
                                                                               (>= z_minus
                                                                                   (+ y_minus
                                                                                      1))))))
                                                          (let ((a!4 (not (and (and true
                                                                                    (= z_minus
                                                                                       0))
                                                                               (not (not a!3)))))
                                                                (a!8 (and (and true
                                                                               (and (= z_plus
                                                                                       0)
                                                                                    (> z_minus
                                                                                       0)))
                                                                          (not (not a!7)))))
                                                            (and a!4 (not a!8)))))))
                                                        (not (and true
                                                                  true
                                                                  false))))
                                             (a!21 (and a!10
                                                        a!16
                                                        (>= x_minus
                                                            (+ y_minus 1))
                                                        (forall ((z_plus Int)
                                                                 (z_minus Int))
                                                          (let ((a!1 (subset (set z_plus)
                                                                             (setunion (setminus emptyset
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!3 (or false
                                                                         (and (>= z_plus
                                                                                  0)
                                                                              (>= x_minus
                                                                                  1))
                                                                         (and (>= z_plus
                                                                                  1)
                                                                              (>= x_minus
                                                                                  0))))
                                                                (a!6 (subset emptyset
                                                                             (setunion (setminus emptyset
                                                                                                 E_S2_plus)
                                                                                       (set (max E_S2_plus)))))
                                                                (a!8 (and (>= x_minus
                                                                              (+ z_minus
                                                                                 1))
                                                                          (>= z_minus
                                                                              (+ y_minus
                                                                                 1)))))
                                                          (let ((a!2 (and (subset emptyset
                                                                                  (setunion (setminus emptyset
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!1))
                                                                (a!7 (and (subset (set z_minus)
                                                                                  (setunion (setminus emptyset
                                                                                                      E_S2_minus)
                                                                                            emptyset))
                                                                          a!6)))
                                                          (let ((a!4 (not (not (and a!2
                                                                                    (and a!3
                                                                                         false)))))
                                                                (a!9 (and (and true
                                                                               (and (= z_plus
                                                                                       0)
                                                                                    (> z_minus
                                                                                       0)))
                                                                          (not (not (and a!7
                                                                                         a!8))))))
                                                          (let ((a!5 (not (and (and true
                                                                                    (= z_minus
                                                                                       0))
                                                                               a!4))))
                                                            (and a!5 (not a!9)))))))
                                                        a!20)))
                                       (let ((a!7 (and (and (and true
                                                                 (= y_minus 0))
                                                            (= x_minus 0))
                                                       (not (not a!6))))
                                             (a!14 (not (and a!8
                                                             (not (not a!13)))))
                                             (a!18 (not (and a!15
                                                             (not (not a!17)))))
                                             (a!22 (not (and a!19
                                                             (not (not a!21))))))
                                         (and (not a!7) a!14 a!18 a!22))))))))
                         (a!131 (and (and (= S1_2_minus
                                             (setunion emptyset emptyset))
                                          a!1)
                                     false
                                     (subset emptyset emptyset)
                                     (subset emptyset E_S1_plus)
                                     (not (and (= S2_minus emptyset)
                                               (= S2_plus emptyset)))
                                     (not (and a!123 (not a!124)))
                                     (and true a!8 a!11)
                                     a!127
                                     (and true a!21)
                                     (and true a!129)
                                     (and true a!28)
                                     a!32
                                     a!130))
                         (a!135 (and (and (= S1_2_minus
                                             (setunion E_S1_minus emptyset))
                                          a!35)
                                     false
                                     (subset emptyset E_S1_minus)
                                     (subset emptyset emptyset)
                                     (not (and (= S2_minus emptyset)
                                               (= S2_plus emptyset)))
                                     (not (and a!133 (not a!134)))
                                     (and true a!41 a!44)
                                     a!127
                                     (and true a!21)
                                     (and true a!129)
                                     (and true a!28)
                                     (and true a!48)
                                     a!130))
                         (a!139 (and (and (= S1_2_minus
                                             (setunion E_S1_minus emptyset))
                                          a!1)
                                     false
                                     (subset emptyset E_S1_minus)
                                     (subset emptyset E_S1_plus)
                                     (not (and (= S2_minus emptyset)
                                               (= S2_plus emptyset)))
                                     (not (and a!137 (not a!138)))
                                     (and true a!54 a!56)
                                     a!127
                                     (and true a!21)
                                     (and true a!129)
                                     (and true a!28)
                                     a!60
                                     a!130))
                         (a!143 (and (and (= S1_2_minus
                                             (setunion emptyset emptyset))
                                          a!35)
                                     false
                                     (subset emptyset emptyset)
                                     (subset emptyset emptyset)
                                     (not (and (= S2_minus emptyset)
                                               (= S2_plus emptyset)))
                                     (not (and a!141 (not a!142)))
                                     (and true a!66 a!68)
                                     a!127
                                     (and true a!21)
                                     (and true a!129)
                                     (and true a!28)
                                     (and true a!71)
                                     a!130)))
                   (let ((a!34 (not (and (and true
                                              (distinct E_S2_plus emptyset)
                                              (= E_S2_minus emptyset))
                                         (and (distinct E_S1_plus emptyset)
                                              (= E_S1_minus emptyset))
                                         (not (not a!33)))))
                         (a!50 (not (and (and true
                                              (distinct E_S2_plus emptyset)
                                              (= E_S2_minus emptyset))
                                         (and (= E_S1_plus emptyset)
                                              (distinct E_S1_minus emptyset))
                                         (not (not a!49)))))
                         (a!62 (not (and (and true
                                              (distinct E_S2_plus emptyset)
                                              (= E_S2_minus emptyset))
                                         (and (distinct E_S1_plus emptyset)
                                              (distinct E_S1_minus emptyset))
                                         (not (not a!61)))))
                         (a!73 (not (and (and true
                                              (distinct E_S2_plus emptyset)
                                              (= E_S2_minus emptyset))
                                         (and (= E_S1_plus emptyset)
                                              (= E_S1_minus emptyset))
                                         (not (not a!72)))))
                         (a!88 (and (and true
                                         (and (= E_S2_plus emptyset)
                                              (distinct E_S2_minus emptyset)))
                                    (and (distinct E_S1_plus emptyset)
                                         (= E_S1_minus emptyset))
                                    (not (not a!87))))
                         (a!92 (and (and true
                                         (and (= E_S2_plus emptyset)
                                              (distinct E_S2_minus emptyset)))
                                    (and (= E_S1_plus emptyset)
                                         (distinct E_S1_minus emptyset))
                                    (not (not a!91))))
                         (a!96 (and (and true
                                         (and (= E_S2_plus emptyset)
                                              (distinct E_S2_minus emptyset)))
                                    (and (distinct E_S1_plus emptyset)
                                         (distinct E_S1_minus emptyset))
                                    (not (not a!95))))
                         (a!100 (and (and true
                                          (and (= E_S2_plus emptyset)
                                               (distinct E_S2_minus emptyset)))
                                     (and (= E_S1_plus emptyset)
                                          (= E_S1_minus emptyset))
                                     (not (not a!99))))
                         (a!110 (not (and (and true
                                               (distinct E_S2_plus emptyset)
                                               (distinct E_S2_minus emptyset))
                                          (and (distinct E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!109)))))
                         (a!114 (not (and (and true
                                               (distinct E_S2_plus emptyset)
                                               (distinct E_S2_minus emptyset))
                                          (and (= E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!113)))))
                         (a!118 (not (and (and true
                                               (distinct E_S2_plus emptyset)
                                               (distinct E_S2_minus emptyset))
                                          (and (distinct E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!117)))))
                         (a!122 (not (and (and true
                                               (distinct E_S2_plus emptyset)
                                               (distinct E_S2_minus emptyset))
                                          (and (= E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!121)))))
                         (a!132 (not (and (and true
                                               (= E_S2_plus emptyset)
                                               (= E_S2_minus emptyset))
                                          (and (distinct E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!131)))))
                         (a!136 (not (and (and true
                                               (= E_S2_plus emptyset)
                                               (= E_S2_minus emptyset))
                                          (and (= E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!135)))))
                         (a!140 (not (and (and true
                                               (= E_S2_plus emptyset)
                                               (= E_S2_minus emptyset))
                                          (and (distinct E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!139)))))
                         (a!144 (not (and (and true
                                               (= E_S2_plus emptyset)
                                               (= E_S2_minus emptyset))
                                          (and (= E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!143))))))
                     (and a!34
                          a!50
                          a!62
                          a!73
                          (not a!88)
                          (not a!92)
                          (not a!96)
                          (not a!100)
                          a!110
                          a!114
                          a!118
                          a!122
                          a!132
                          a!136
                          a!140
                          a!144))))))))))
(let ((a!3 (or (= (max S1_plus) (+ (max S2_plus) 5))
               (and (= S2_plus emptyset) a!1)
               a!2))
      (a!8 (or (= (max S1_plus) (+ (max S2_plus) 1))
               (and (= S2_plus emptyset) a!6)
               a!7))
      (a!13 (or (= (max S1_plus) (+ (max S1_1_plus) 1))
                (and (= S1_1_plus emptyset) a!11)
                a!12))
      (a!17 (or (= (max S1_1_plus) (+ (max S1_2_plus) 1))
                (and (= S1_2_plus emptyset) a!15)
                a!16))
      (a!21 (or a!19
                (and (= S1_2_minus emptyset) a!20)
                (and (distinct S1_2_minus emptyset)
                     (= S2_minus emptyset)
                     (distinct S2_plus emptyset))
                (<= (max S2_minus) (+ (max S1_2_minus) 0))))
      (a!24 (or a!22
                (and (= S2_minus emptyset) a!23)
                (and (distinct S2_minus emptyset)
                     (= S1_2_minus emptyset)
                     (distinct S1_2_plus emptyset))
                (<= (max S1_2_minus) (+ (max S2_minus) 0))))
      (a!27 (or a!25
                false
                (and (>= (min S1_2_plus) 0) (>= (max S1_2_minus) 1))
                (and (>= (min S1_2_plus) 1) (>= (max S1_2_minus) 0))
                a!26))
      (a!33 (or a!31
                false
                (and (>= (min S1_2_plus) 0) (>= (max S2_minus) 1))
                (and (>= (min S1_2_plus) 1) (>= (max S2_minus) 0))
                a!32))
      (a!37 (or a!34
                (and (and (= S2_minus emptyset) (= S2_plus emptyset)) a!35)
                (and (distinct S2_minus emptyset) (distinct S2_plus emptyset))
                a!36))
      (a!40 (or (<= (max S1_2_plus) (+ (max S2_plus) 1))
                (and (= S2_plus emptyset) a!38)
                (and (and (= S1_2_plus emptyset) (distinct S1_2_minus emptyset))
                     (distinct S2_plus emptyset))
                a!39))
      (a!43 (or (>= (max S1_2_plus) (+ (max S2_plus) 1))
                (and (= S2_plus emptyset) a!41)
                a!42)))
(let ((a!9 (not (and (and |[E,0]| (>= E_plus 1))
                     (= S1_minus (setunion S2_minus emptyset))
                     a!5
                     a!8)))
      (a!44 (and (= S1_2_minus (setunion S2_minus emptyset))
                 a!18
                 true
                 a!21
                 a!24
                 (and true a!27)
                 true
                 (or a!28
                     (and (= S1_2_minus emptyset) (= S2_plus emptyset) a!29)
                     (and (distinct S1_2_minus emptyset)
                          (distinct S2_plus emptyset))
                     a!30)
                 true
                 a!33
                 (and true a!37)
                 true
                 a!40
                 a!43)))
(let ((a!46 (and (not (and (= S1_2_minus S2_minus) (= S1_2_plus S2_plus)))
                 (not a!44)
                 (not a!45))))
(let ((a!47 (not (and (and |[E,0]| (>= E_plus 1))
                      (= S1_minus (setunion S1_1_minus emptyset))
                      a!10
                      a!13
                      (= S1_1_minus (setunion S1_2_minus emptyset))
                      a!14
                      a!17
                      (not a!46)))))
  (and a!3
       (not (and a!4 a!9 a!47))
       true
       (= E_minus 0)
       (= F_minus 0)
       (distinct S1_plus emptyset)
       (distinct S1_minus emptyset)
       (distinct S2_plus emptyset)
       (distinct S2_minus emptyset)
       (distinct S1_1_plus emptyset)
       (distinct S1_1_minus emptyset)
       (distinct S1_2_plus emptyset)
       (distinct S1_2_minus emptyset)))))))
