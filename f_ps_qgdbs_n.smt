(let ((a!1 (not (and (not |[E,0]|)
                     (= E_plus (+ F_plus 0))
                     (= emptyset emptyset)
                     (= S1_plus S2_plus))))
      (a!2 (setunion S2_plus (setunion (set (min S1_plus)) (set (max S1_plus)))))
      (a!3 (and (= emptyset emptyset) (>= (max S1_plus) (+ (min S1_plus) 10))))
      (a!4 (and (= S1_plus emptyset) (>= (max emptyset) (+ (min emptyset) 10))))
      (a!7 (setunion S1_1_plus
                     (setunion (set (min S1_plus)) (set (max S1_plus)))))
      (a!8 (setunion S1_2_plus
                     (setunion (set (min S1_1_plus)) (set (max S1_1_plus)))))
      (a!9 (and (= emptyset emptyset)
                (>= (max S1_1_plus) (+ (min S1_1_plus) 10))))
      (a!10 (and (= S1_1_plus emptyset)
                 (>= (max emptyset) (+ (min emptyset) 10))))
      (a!12 (and (not (and (= emptyset emptyset) (= S1_2_plus S2_plus)))
                 (forall ((E_S3_plus SetInt)
                          (E_S3_minus SetInt)
                          (E_S2_plus SetInt)
                          (E_S2_minus SetInt)
                          (E_S1_plus SetInt)
                          (E_S1_minus SetInt))
                   (let ((a!1 (and (and true
                                        (distinct E_S3_plus emptyset)
                                        (= E_S3_minus emptyset))
                                   (and (distinct E_S2_plus emptyset)
                                        (= E_S2_minus emptyset))))
                         (a!2 (setunion S2_plus
                                        (setunion (set (min E_S2_plus))
                                                  (set (max E_S2_plus)))))
                         (a!4 (and true
                                   true
                                   (>= (max S1_2_plus) (+ (min S1_2_plus) 10))
                                   (<= (max S1_2_plus) (+ (min S1_2_plus) 100))
                                   true
                                   true
                                   true
                                   true))
                         (a!5 (and true
                                   true
                                   (>= (max E_S2_plus) (+ (min E_S2_plus) 10))
                                   (<= (max E_S2_plus) (+ (min E_S2_plus) 100))
                                   true
                                   true
                                   true
                                   true))
                         (a!6 (and (not (and (= emptyset emptyset)
                                             (= E_S1_plus emptyset)))
                                   (>= (max E_S1_plus) (+ (min E_S2_plus) 0))))
                         (a!7 (and (not (and (= emptyset emptyset)
                                             (= E_S3_plus emptyset)))
                                   (>= (max E_S2_plus) (+ (min E_S3_plus) 0))))
                         (a!10 (or false
                                   (and (<= (min E_S1_minus) 0)
                                        (<= (min E_S2_plus) 0))))
                         (a!14 (and (not (and (= E_S1_minus emptyset)
                                              (= E_S1_plus emptyset)))
                                    (>= (max E_S1_plus) (+ (min E_S2_plus) 0))))
                         (a!17 (and (not (and (= emptyset emptyset)
                                              (= emptyset emptyset)))
                                    false))
                         (a!20 (and (and true
                                         (distinct E_S3_plus emptyset)
                                         (= E_S3_minus emptyset))
                                    (and (= E_S2_plus emptyset)
                                         (distinct E_S2_minus emptyset))))
                         (a!21 (setunion emptyset
                                         (setunion (set (max E_S2_minus))
                                                   (set (min E_S2_minus)))))
                         (a!23 (and true
                                    true
                                    (>= (max E_S2_minus)
                                        (+ (min E_S2_minus) 10))
                                    (<= (max E_S2_minus)
                                        (+ (min E_S2_minus) 100))
                                    true
                                    true
                                    true
                                    true))
                         (a!24 (or false
                                   (and (>= (max E_S1_plus) 0)
                                        (>= (max E_S2_minus) 0))))
                         (a!26 (or false
                                   (and (<= (min E_S2_minus) 0)
                                        (<= (min E_S3_plus) 0))))
                         (a!30 (and (not (and (= E_S1_minus emptyset)
                                              (= emptyset emptyset)))
                                    (>= (max E_S2_minus) (+ (min E_S1_minus) 0))))
                         (a!38 (and (and true
                                         (distinct E_S3_plus emptyset)
                                         (= E_S3_minus emptyset))
                                    (and (distinct E_S2_plus emptyset)
                                         (distinct E_S2_minus emptyset))))
                         (a!39 (setunion emptyset
                                         (setunion (set (max E_S2_minus))
                                                   emptyset)))
                         (a!40 (setunion S2_plus
                                         (setunion emptyset
                                                   (set (max E_S2_plus)))))
                         (a!41 (or false
                                   (and (>= (max E_S2_plus) 0)
                                        (>= (max E_S2_minus) 10))
                                   (and (>= (max E_S2_plus) 1)
                                        (>= (max E_S2_minus) 9))
                                   (and (>= (max E_S2_plus) 2)
                                        (>= (max E_S2_minus) 8))
                                   (and (>= (max E_S2_plus) 3)
                                        (>= (max E_S2_minus) 7))
                                   (and (>= (max E_S2_plus) 4)
                                        (>= (max E_S2_minus) 6))
                                   (and (>= (max E_S2_plus) 5)
                                        (>= (max E_S2_minus) 5))
                                   (and (>= (max E_S2_plus) 6)
                                        (>= (max E_S2_minus) 4))
                                   (and (>= (max E_S2_plus) 7)
                                        (>= (max E_S2_minus) 3))
                                   (and (>= (max E_S2_plus) 8)
                                        (>= (max E_S2_minus) 2))
                                   (and (>= (max E_S2_plus) 9)
                                        (>= (max E_S2_minus) 1))
                                   (and (>= (max E_S2_plus) 10)
                                        (>= (max E_S2_minus) 0))))
                         (a!42 (or false
                                   (and (<= (max E_S2_plus) 0)
                                        (<= (max E_S2_minus) 100))
                                   (and (<= (max E_S2_plus) 1)
                                        (<= (max E_S2_minus) 99))
                                   (and (<= (max E_S2_plus) 2)
                                        (<= (max E_S2_minus) 98))
                                   (and (<= (max E_S2_plus) 3)
                                        (<= (max E_S2_minus) 97))
                                   (and (<= (max E_S2_plus) 4)
                                        (<= (max E_S2_minus) 96))
                                   (and (<= (max E_S2_plus) 5)
                                        (<= (max E_S2_minus) 95))
                                   (and (<= (max E_S2_plus) 6)
                                        (<= (max E_S2_minus) 94))
                                   (and (<= (max E_S2_plus) 7)
                                        (<= (max E_S2_minus) 93))
                                   (and (<= (max E_S2_plus) 8)
                                        (<= (max E_S2_minus) 92))
                                   (and (<= (max E_S2_plus) 9)
                                        (<= (max E_S2_minus) 91))
                                   (and (<= (max E_S2_plus) 10)
                                        (<= (max E_S2_minus) 90))
                                   (and (<= (max E_S2_plus) 11)
                                        (<= (max E_S2_minus) 89))
                                   (and (<= (max E_S2_plus) 12)
                                        (<= (max E_S2_minus) 88))
                                   (and (<= (max E_S2_plus) 13)
                                        (<= (max E_S2_minus) 87))
                                   (and (<= (max E_S2_plus) 14)
                                        (<= (max E_S2_minus) 86))
                                   (and (<= (max E_S2_plus) 15)
                                        (<= (max E_S2_minus) 85))
                                   (and (<= (max E_S2_plus) 16)
                                        (<= (max E_S2_minus) 84))
                                   (and (<= (max E_S2_plus) 17)
                                        (<= (max E_S2_minus) 83))
                                   (and (<= (max E_S2_plus) 18)
                                        (<= (max E_S2_minus) 82))
                                   (and (<= (max E_S2_plus) 19)
                                        (<= (max E_S2_minus) 81))
                                   (and (<= (max E_S2_plus) 20)
                                        (<= (max E_S2_minus) 80))
                                   (and (<= (max E_S2_plus) 21)
                                        (<= (max E_S2_minus) 79))
                                   (and (<= (max E_S2_plus) 22)
                                        (<= (max E_S2_minus) 78))
                                   (and (<= (max E_S2_plus) 23)
                                        (<= (max E_S2_minus) 77))
                                   (and (<= (max E_S2_plus) 24)
                                        (<= (max E_S2_minus) 76))
                                   (and (<= (max E_S2_plus) 25)
                                        (<= (max E_S2_minus) 75))
                                   (and (<= (max E_S2_plus) 26)
                                        (<= (max E_S2_minus) 74))
                                   (and (<= (max E_S2_plus) 27)
                                        (<= (max E_S2_minus) 73))
                                   (and (<= (max E_S2_plus) 28)
                                        (<= (max E_S2_minus) 72))
                                   (and (<= (max E_S2_plus) 29)
                                        (<= (max E_S2_minus) 71))
                                   (and (<= (max E_S2_plus) 30)
                                        (<= (max E_S2_minus) 70))
                                   (and (<= (max E_S2_plus) 31)
                                        (<= (max E_S2_minus) 69))
                                   (and (<= (max E_S2_plus) 32)
                                        (<= (max E_S2_minus) 68))
                                   (and (<= (max E_S2_plus) 33)
                                        (<= (max E_S2_minus) 67))
                                   (and (<= (max E_S2_plus) 34)
                                        (<= (max E_S2_minus) 66))
                                   (and (<= (max E_S2_plus) 35)
                                        (<= (max E_S2_minus) 65))
                                   (and (<= (max E_S2_plus) 36)
                                        (<= (max E_S2_minus) 64))
                                   (and (<= (max E_S2_plus) 37)
                                        (<= (max E_S2_minus) 63))
                                   (and (<= (max E_S2_plus) 38)
                                        (<= (max E_S2_minus) 62))
                                   (and (<= (max E_S2_plus) 39)
                                        (<= (max E_S2_minus) 61))
                                   (and (<= (max E_S2_plus) 40)
                                        (<= (max E_S2_minus) 60))
                                   (and (<= (max E_S2_plus) 41)
                                        (<= (max E_S2_minus) 59))
                                   (and (<= (max E_S2_plus) 42)
                                        (<= (max E_S2_minus) 58))
                                   (and (<= (max E_S2_plus) 43)
                                        (<= (max E_S2_minus) 57))
                                   (and (<= (max E_S2_plus) 44)
                                        (<= (max E_S2_minus) 56))
                                   (and (<= (max E_S2_plus) 45)
                                        (<= (max E_S2_minus) 55))
                                   (and (<= (max E_S2_plus) 46)
                                        (<= (max E_S2_minus) 54))
                                   (and (<= (max E_S2_plus) 47)
                                        (<= (max E_S2_minus) 53))
                                   (and (<= (max E_S2_plus) 48)
                                        (<= (max E_S2_minus) 52))
                                   (and (<= (max E_S2_plus) 49)
                                        (<= (max E_S2_minus) 51))
                                   (and (<= (max E_S2_plus) 50)
                                        (<= (max E_S2_minus) 50))
                                   (and (<= (max E_S2_plus) 51)
                                        (<= (max E_S2_minus) 49))
                                   (and (<= (max E_S2_plus) 52)
                                        (<= (max E_S2_minus) 48))
                                   (and (<= (max E_S2_plus) 53)
                                        (<= (max E_S2_minus) 47))
                                   (and (<= (max E_S2_plus) 54)
                                        (<= (max E_S2_minus) 46))
                                   (and (<= (max E_S2_plus) 55)
                                        (<= (max E_S2_minus) 45))
                                   (and (<= (max E_S2_plus) 56)
                                        (<= (max E_S2_minus) 44))
                                   (and (<= (max E_S2_plus) 57)
                                        (<= (max E_S2_minus) 43))
                                   (and (<= (max E_S2_plus) 58)
                                        (<= (max E_S2_minus) 42))
                                   (and (<= (max E_S2_plus) 59)
                                        (<= (max E_S2_minus) 41))
                                   (and (<= (max E_S2_plus) 60)
                                        (<= (max E_S2_minus) 40))
                                   (and (<= (max E_S2_plus) 61)
                                        (<= (max E_S2_minus) 39))
                                   (and (<= (max E_S2_plus) 62)
                                        (<= (max E_S2_minus) 38))
                                   (and (<= (max E_S2_plus) 63)
                                        (<= (max E_S2_minus) 37))
                                   (and (<= (max E_S2_plus) 64)
                                        (<= (max E_S2_minus) 36))
                                   (and (<= (max E_S2_plus) 65)
                                        (<= (max E_S2_minus) 35))
                                   (and (<= (max E_S2_plus) 66)
                                        (<= (max E_S2_minus) 34))
                                   (and (<= (max E_S2_plus) 67)
                                        (<= (max E_S2_minus) 33))
                                   (and (<= (max E_S2_plus) 68)
                                        (<= (max E_S2_minus) 32))
                                   (and (<= (max E_S2_plus) 69)
                                        (<= (max E_S2_minus) 31))
                                   (and (<= (max E_S2_plus) 70)
                                        (<= (max E_S2_minus) 30))
                                   (and (<= (max E_S2_plus) 71)
                                        (<= (max E_S2_minus) 29))
                                   (and (<= (max E_S2_plus) 72)
                                        (<= (max E_S2_minus) 28))
                                   (and (<= (max E_S2_plus) 73)
                                        (<= (max E_S2_minus) 27))
                                   (and (<= (max E_S2_plus) 74)
                                        (<= (max E_S2_minus) 26))
                                   (and (<= (max E_S2_plus) 75)
                                        (<= (max E_S2_minus) 25))
                                   (and (<= (max E_S2_plus) 76)
                                        (<= (max E_S2_minus) 24))
                                   (and (<= (max E_S2_plus) 77)
                                        (<= (max E_S2_minus) 23))
                                   (and (<= (max E_S2_plus) 78)
                                        (<= (max E_S2_minus) 22))
                                   (and (<= (max E_S2_plus) 79)
                                        (<= (max E_S2_minus) 21))
                                   (and (<= (max E_S2_plus) 80)
                                        (<= (max E_S2_minus) 20))
                                   (and (<= (max E_S2_plus) 81)
                                        (<= (max E_S2_minus) 19))
                                   (and (<= (max E_S2_plus) 82)
                                        (<= (max E_S2_minus) 18))
                                   (and (<= (max E_S2_plus) 83)
                                        (<= (max E_S2_minus) 17))
                                   (and (<= (max E_S2_plus) 84)
                                        (<= (max E_S2_minus) 16))
                                   (and (<= (max E_S2_plus) 85)
                                        (<= (max E_S2_minus) 15))
                                   (and (<= (max E_S2_plus) 86)
                                        (<= (max E_S2_minus) 14))
                                   (and (<= (max E_S2_plus) 87)
                                        (<= (max E_S2_minus) 13))
                                   (and (<= (max E_S2_plus) 88)
                                        (<= (max E_S2_minus) 12))
                                   (and (<= (max E_S2_plus) 89)
                                        (<= (max E_S2_minus) 11))
                                   (and (<= (max E_S2_plus) 90)
                                        (<= (max E_S2_minus) 10))
                                   (and (<= (max E_S2_plus) 91)
                                        (<= (max E_S2_minus) 9))
                                   (and (<= (max E_S2_plus) 92)
                                        (<= (max E_S2_minus) 8))
                                   (and (<= (max E_S2_plus) 93)
                                        (<= (max E_S2_minus) 7))
                                   (and (<= (max E_S2_plus) 94)
                                        (<= (max E_S2_minus) 6))
                                   (and (<= (max E_S2_plus) 95)
                                        (<= (max E_S2_minus) 5))
                                   (and (<= (max E_S2_plus) 96)
                                        (<= (max E_S2_minus) 4))
                                   (and (<= (max E_S2_plus) 97)
                                        (<= (max E_S2_minus) 3))
                                   (and (<= (max E_S2_plus) 98)
                                        (<= (max E_S2_minus) 2))
                                   (and (<= (max E_S2_plus) 99)
                                        (<= (max E_S2_minus) 1))
                                   (and (<= (max E_S2_plus) 100)
                                        (<= (max E_S2_minus) 0))))
                         (a!51 (and (and true
                                         (distinct E_S3_plus emptyset)
                                         (= E_S3_minus emptyset))
                                    (and (= E_S2_plus emptyset)
                                         (= E_S2_minus emptyset))))
                         (a!52 (and (not (and (= emptyset emptyset)
                                              (= E_S1_plus emptyset)))
                                    false))
                         (a!53 (and (not (and (= emptyset emptyset)
                                              (= E_S3_plus emptyset)))
                                    false))
                         (a!56 (and (not (and (= E_S1_minus emptyset)
                                              (= emptyset emptyset)))
                                    false))
                         (a!59 (and (not (and (= E_S1_minus emptyset)
                                              (= E_S1_plus emptyset)))
                                    false))
                         (a!64 (and (and true
                                         (= E_S3_plus emptyset)
                                         (distinct E_S3_minus emptyset))
                                    (and (distinct E_S2_plus emptyset)
                                         (= E_S2_minus emptyset))))
                         (a!65 (or false
                                   (and (>= (max E_S2_plus) 0)
                                        (>= (max E_S3_minus) 0))))
                         (a!75 (and (and true
                                         (= E_S3_plus emptyset)
                                         (distinct E_S3_minus emptyset))
                                    (and (= E_S2_plus emptyset)
                                         (distinct E_S2_minus emptyset))))
                         (a!76 (and (not (and (= E_S3_minus emptyset)
                                              (= emptyset emptyset)))
                                    (>= (max E_S3_minus) (+ (min E_S2_minus) 0))))
                         (a!85 (and (and true
                                         (= E_S3_plus emptyset)
                                         (distinct E_S3_minus emptyset))
                                    (and (distinct E_S2_plus emptyset)
                                         (distinct E_S2_minus emptyset))))
                         (a!94 (and (and true
                                         (= E_S3_plus emptyset)
                                         (distinct E_S3_minus emptyset))
                                    (and (= E_S2_plus emptyset)
                                         (= E_S2_minus emptyset))))
                         (a!95 (and (not (and (= E_S3_minus emptyset)
                                              (= emptyset emptyset)))
                                    false))
                         (a!104 (and (and true
                                          (distinct E_S3_plus emptyset)
                                          (distinct E_S3_minus emptyset))
                                     (and (distinct E_S2_plus emptyset)
                                          (= E_S2_minus emptyset))))
                         (a!114 (and (and true
                                          (distinct E_S3_plus emptyset)
                                          (distinct E_S3_minus emptyset))
                                     (and (= E_S2_plus emptyset)
                                          (distinct E_S2_minus emptyset))))
                         (a!115 (and (not (and (= E_S3_minus emptyset)
                                               (= E_S3_plus emptyset)))
                                     (>= (max E_S3_minus)
                                         (+ (min E_S2_minus) 0))))
                         (a!124 (and (and true
                                          (distinct E_S3_plus emptyset)
                                          (distinct E_S3_minus emptyset))
                                     (and (distinct E_S2_plus emptyset)
                                          (distinct E_S2_minus emptyset))))
                         (a!133 (and (and true
                                          (distinct E_S3_plus emptyset)
                                          (distinct E_S3_minus emptyset))
                                     (and (= E_S2_plus emptyset)
                                          (= E_S2_minus emptyset))))
                         (a!134 (and (not (and (= E_S3_minus emptyset)
                                               (= E_S3_plus emptyset)))
                                     false))
                         (a!143 (and (and true
                                          (= E_S3_plus emptyset)
                                          (= E_S3_minus emptyset))
                                     (and (distinct E_S2_plus emptyset)
                                          (= E_S2_minus emptyset))))
                         (a!152 (and (and true
                                          (= E_S3_plus emptyset)
                                          (= E_S3_minus emptyset))
                                     (and (= E_S2_plus emptyset)
                                          (distinct E_S2_minus emptyset))))
                         (a!161 (and (and true
                                          (= E_S3_plus emptyset)
                                          (= E_S3_minus emptyset))
                                     (and (distinct E_S2_plus emptyset)
                                          (distinct E_S2_minus emptyset))))
                         (a!170 (and (and true
                                          (= E_S3_plus emptyset)
                                          (= E_S3_minus emptyset))
                                     (and (= E_S2_plus emptyset)
                                          (= E_S2_minus emptyset)))))
                   (let ((a!3 (and (= emptyset
                                      (setunion emptyset
                                                (setunion emptyset emptyset)))
                                   (= E_S2_plus a!2)))
                         (a!11 (and (not (and (= E_S1_minus emptyset)
                                              (= emptyset emptyset)))
                                    a!10))
                         (a!22 (and (= E_S2_minus a!21)
                                    (= emptyset
                                       (setunion S2_plus
                                                 (setunion emptyset emptyset)))))
                         (a!25 (and (not (and (= emptyset emptyset)
                                              (= E_S1_plus emptyset)))
                                    a!24))
                         (a!27 (and (not (and (= emptyset emptyset)
                                              (= E_S3_plus emptyset)))
                                    a!26))
                         (a!33 (and (not (and (= E_S1_minus emptyset)
                                              (= E_S1_plus emptyset)))
                                    a!24))
                         (a!45 (and (and (= E_S2_minus a!39) (= E_S2_plus a!40))
                                    (= emptyset
                                       (setunion (setunion E_S1_minus
                                                           E_S2_minus)
                                                 emptyset))
                                    (= S1_2_plus
                                       (setunion (setunion emptyset E_S2_plus)
                                                 E_S3_plus))
                                    a!4
                                    (and true
                                         true
                                         a!41
                                         a!42
                                         true
                                         true
                                         true
                                         true)
                                    (not a!30)
                                    (not a!7)))
                         (a!49 (and (and (= E_S2_minus a!39) (= E_S2_plus a!40))
                                    (= emptyset
                                       (setunion (setunion emptyset E_S2_minus)
                                                 emptyset))
                                    (= S1_2_plus
                                       (setunion (setunion emptyset E_S2_plus)
                                                 E_S3_plus))
                                    a!4
                                    (and true
                                         true
                                         a!41
                                         a!42
                                         true
                                         true
                                         true
                                         true)
                                    (not a!17)
                                    (not a!7)))
                         (a!54 (and false
                                    (= emptyset
                                       (setunion (setunion emptyset emptyset)
                                                 emptyset))
                                    (= S1_2_plus
                                       (setunion (setunion E_S1_plus emptyset)
                                                 E_S3_plus))
                                    a!4
                                    (and true
                                         true
                                         false
                                         false
                                         true
                                         true
                                         true
                                         true)
                                    (not a!52)
                                    (not a!53)))
                         (a!57 (and false
                                    (= emptyset
                                       (setunion (setunion E_S1_minus emptyset)
                                                 emptyset))
                                    (= S1_2_plus
                                       (setunion (setunion emptyset emptyset)
                                                 E_S3_plus))
                                    a!4
                                    (and true
                                         true
                                         false
                                         false
                                         true
                                         true
                                         true
                                         true)
                                    (not a!56)
                                    (not a!53)))
                         (a!60 (and false
                                    (= emptyset
                                       (setunion (setunion E_S1_minus emptyset)
                                                 emptyset))
                                    (= S1_2_plus
                                       (setunion (setunion E_S1_plus emptyset)
                                                 E_S3_plus))
                                    a!4
                                    (and true
                                         true
                                         false
                                         false
                                         true
                                         true
                                         true
                                         true)
                                    (not a!59)
                                    (not a!53)))
                         (a!62 (and false
                                    (= emptyset
                                       (setunion (setunion emptyset emptyset)
                                                 emptyset))
                                    (= S1_2_plus
                                       (setunion (setunion emptyset emptyset)
                                                 E_S3_plus))
                                    a!4
                                    (and true
                                         true
                                         false
                                         false
                                         true
                                         true
                                         true
                                         true)
                                    (not a!17)
                                    (not a!53)))
                         (a!66 (and (not (and (= E_S3_minus emptyset)
                                              (= emptyset emptyset)))
                                    a!65))
                         (a!96 (and false
                                    (= emptyset
                                       (setunion (setunion emptyset emptyset)
                                                 E_S3_minus))
                                    (= S1_2_plus
                                       (setunion (setunion E_S1_plus emptyset)
                                                 emptyset))
                                    a!4
                                    (and true
                                         true
                                         false
                                         false
                                         true
                                         true
                                         true
                                         true)
                                    (not a!52)
                                    (not a!95)))
                         (a!98 (and false
                                    (= emptyset
                                       (setunion (setunion E_S1_minus emptyset)
                                                 E_S3_minus))
                                    (= S1_2_plus
                                       (setunion (setunion emptyset emptyset)
                                                 emptyset))
                                    a!4
                                    (and true
                                         true
                                         false
                                         false
                                         true
                                         true
                                         true
                                         true)
                                    (not a!56)
                                    (not a!95)))
                         (a!100 (and false
                                     (= emptyset
                                        (setunion (setunion E_S1_minus emptyset)
                                                  E_S3_minus))
                                     (= S1_2_plus
                                        (setunion (setunion E_S1_plus emptyset)
                                                  emptyset))
                                     a!4
                                     (and true
                                          true
                                          false
                                          false
                                          true
                                          true
                                          true
                                          true)
                                     (not a!59)
                                     (not a!95)))
                         (a!102 (and false
                                     (= emptyset
                                        (setunion (setunion emptyset emptyset)
                                                  E_S3_minus))
                                     (= S1_2_plus
                                        (setunion (setunion emptyset emptyset)
                                                  emptyset))
                                     a!4
                                     (and true
                                          true
                                          false
                                          false
                                          true
                                          true
                                          true
                                          true)
                                     (not a!17)
                                     (not a!95)))
                         (a!105 (and (not (and (= E_S3_minus emptyset)
                                               (= E_S3_plus emptyset)))
                                     a!65))
                         (a!135 (and false
                                     (= emptyset
                                        (setunion (setunion emptyset emptyset)
                                                  E_S3_minus))
                                     (= S1_2_plus
                                        (setunion (setunion E_S1_plus emptyset)
                                                  E_S3_plus))
                                     a!4
                                     (and true
                                          true
                                          false
                                          false
                                          true
                                          true
                                          true
                                          true)
                                     (not a!52)
                                     (not a!134)))
                         (a!137 (and false
                                     (= emptyset
                                        (setunion (setunion E_S1_minus emptyset)
                                                  E_S3_minus))
                                     (= S1_2_plus
                                        (setunion (setunion emptyset emptyset)
                                                  E_S3_plus))
                                     a!4
                                     (and true
                                          true
                                          false
                                          false
                                          true
                                          true
                                          true
                                          true)
                                     (not a!56)
                                     (not a!134)))
                         (a!139 (and false
                                     (= emptyset
                                        (setunion (setunion E_S1_minus emptyset)
                                                  E_S3_minus))
                                     (= S1_2_plus
                                        (setunion (setunion E_S1_plus emptyset)
                                                  E_S3_plus))
                                     a!4
                                     (and true
                                          true
                                          false
                                          false
                                          true
                                          true
                                          true
                                          true)
                                     (not a!59)
                                     (not a!134)))
                         (a!141 (and false
                                     (= emptyset
                                        (setunion (setunion emptyset emptyset)
                                                  E_S3_minus))
                                     (= S1_2_plus
                                        (setunion (setunion emptyset emptyset)
                                                  E_S3_plus))
                                     a!4
                                     (and true
                                          true
                                          false
                                          false
                                          true
                                          true
                                          true
                                          true)
                                     (not a!17)
                                     (not a!134)))
                         (a!164 (and (and (= E_S2_minus a!39)
                                          (= E_S2_plus a!40))
                                     (= emptyset
                                        (setunion (setunion E_S1_minus
                                                            E_S2_minus)
                                                  emptyset))
                                     (= S1_2_plus
                                        (setunion (setunion emptyset E_S2_plus)
                                                  emptyset))
                                     a!4
                                     (and true
                                          true
                                          a!41
                                          a!42
                                          true
                                          true
                                          true
                                          true)
                                     (not a!30)
                                     (not a!17)))
                         (a!168 (and (and (= E_S2_minus a!39)
                                          (= E_S2_plus a!40))
                                     (= emptyset
                                        (setunion (setunion emptyset E_S2_minus)
                                                  emptyset))
                                     (= S1_2_plus
                                        (setunion (setunion emptyset E_S2_plus)
                                                  emptyset))
                                     a!4
                                     (and true
                                          true
                                          a!41
                                          a!42
                                          true
                                          true
                                          true
                                          true)
                                     (not a!17)
                                     (not a!17)))
                         (a!171 (and false
                                     (= emptyset
                                        (setunion (setunion emptyset emptyset)
                                                  emptyset))
                                     (= S1_2_plus
                                        (setunion (setunion E_S1_plus emptyset)
                                                  emptyset))
                                     a!4
                                     (and true
                                          true
                                          false
                                          false
                                          true
                                          true
                                          true
                                          true)
                                     (not a!52)
                                     (not a!17)))
                         (a!173 (and false
                                     (= emptyset
                                        (setunion (setunion E_S1_minus emptyset)
                                                  emptyset))
                                     (= S1_2_plus
                                        (setunion (setunion emptyset emptyset)
                                                  emptyset))
                                     a!4
                                     (and true
                                          true
                                          false
                                          false
                                          true
                                          true
                                          true
                                          true)
                                     (not a!56)
                                     (not a!17)))
                         (a!175 (and false
                                     (= emptyset
                                        (setunion (setunion E_S1_minus emptyset)
                                                  emptyset))
                                     (= S1_2_plus
                                        (setunion (setunion E_S1_plus emptyset)
                                                  emptyset))
                                     a!4
                                     (and true
                                          true
                                          false
                                          false
                                          true
                                          true
                                          true
                                          true)
                                     (not a!59)
                                     (not a!17)))
                         (a!177 (and false
                                     (= emptyset
                                        (setunion (setunion emptyset emptyset)
                                                  emptyset))
                                     (= S1_2_plus
                                        (setunion (setunion emptyset emptyset)
                                                  emptyset))
                                     a!4
                                     (and true
                                          true
                                          false
                                          false
                                          true
                                          true
                                          true
                                          true)
                                     (not a!17)
                                     (not a!17))))
                   (let ((a!8 (and a!3
                                   (= emptyset
                                      (setunion (setunion emptyset emptyset)
                                                emptyset))
                                   (= S1_2_plus
                                      (setunion (setunion E_S1_plus E_S2_plus)
                                                E_S3_plus))
                                   a!4
                                   a!5
                                   (not a!6)
                                   (not a!7)))
                         (a!12 (and a!3
                                    (= emptyset
                                       (setunion (setunion E_S1_minus emptyset)
                                                 emptyset))
                                    (= S1_2_plus
                                       (setunion (setunion emptyset E_S2_plus)
                                                 E_S3_plus))
                                    a!4
                                    a!5
                                    (not a!11)
                                    (not a!7)))
                         (a!15 (and a!3
                                    (= emptyset
                                       (setunion (setunion E_S1_minus emptyset)
                                                 emptyset))
                                    (= S1_2_plus
                                       (setunion (setunion E_S1_plus E_S2_plus)
                                                 E_S3_plus))
                                    a!4
                                    a!5
                                    (not a!14)
                                    (not a!7)))
                         (a!18 (and a!3
                                    (= emptyset
                                       (setunion (setunion emptyset emptyset)
                                                 emptyset))
                                    (= S1_2_plus
                                       (setunion (setunion emptyset E_S2_plus)
                                                 E_S3_plus))
                                    a!4
                                    a!5
                                    (not a!17)
                                    (not a!7)))
                         (a!28 (and a!22
                                    (= emptyset
                                       (setunion (setunion emptyset E_S2_minus)
                                                 emptyset))
                                    (= S1_2_plus
                                       (setunion (setunion E_S1_plus emptyset)
                                                 E_S3_plus))
                                    a!4
                                    a!23
                                    (not a!25)
                                    (not a!27)))
                         (a!31 (and a!22
                                    (= emptyset
                                       (setunion (setunion E_S1_minus
                                                           E_S2_minus)
                                                 emptyset))
                                    (= S1_2_plus
                                       (setunion (setunion emptyset emptyset)
                                                 E_S3_plus))
                                    a!4
                                    a!23
                                    (not a!30)
                                    (not a!27)))
                         (a!34 (and a!22
                                    (= emptyset
                                       (setunion (setunion E_S1_minus
                                                           E_S2_minus)
                                                 emptyset))
                                    (= S1_2_plus
                                       (setunion (setunion E_S1_plus emptyset)
                                                 E_S3_plus))
                                    a!4
                                    a!23
                                    (not a!33)
                                    (not a!27)))
                         (a!36 (and a!22
                                    (= emptyset
                                       (setunion (setunion emptyset E_S2_minus)
                                                 emptyset))
                                    (= S1_2_plus
                                       (setunion (setunion emptyset emptyset)
                                                 E_S3_plus))
                                    a!4
                                    a!23
                                    (not a!17)
                                    (not a!27)))
                         (a!43 (and (and (= E_S2_minus a!39) (= E_S2_plus a!40))
                                    (= emptyset
                                       (setunion (setunion emptyset E_S2_minus)
                                                 emptyset))
                                    (= S1_2_plus
                                       (setunion (setunion E_S1_plus E_S2_plus)
                                                 E_S3_plus))
                                    a!4
                                    (and true
                                         true
                                         a!41
                                         a!42
                                         true
                                         true
                                         true
                                         true)
                                    (not a!25)
                                    (not a!7)))
                         (a!46 (not (and a!38
                                         (and (= E_S1_plus emptyset)
                                              (distinct E_S1_minus emptyset))
                                         (not (not a!45)))))
                         (a!47 (and (and (= E_S2_minus a!39) (= E_S2_plus a!40))
                                    (= emptyset
                                       (setunion (setunion E_S1_minus
                                                           E_S2_minus)
                                                 emptyset))
                                    (= S1_2_plus
                                       (setunion (setunion E_S1_plus E_S2_plus)
                                                 E_S3_plus))
                                    a!4
                                    (and true
                                         true
                                         a!41
                                         a!42
                                         true
                                         true
                                         true
                                         true)
                                    (not a!33)
                                    (not a!7)))
                         (a!50 (not (and a!38
                                         (and (= E_S1_plus emptyset)
                                              (= E_S1_minus emptyset))
                                         (not (not a!49)))))
                         (a!55 (not (and a!51
                                         (and (distinct E_S1_plus emptyset)
                                              (= E_S1_minus emptyset))
                                         (not (not a!54)))))
                         (a!58 (not (and a!51
                                         (and (= E_S1_plus emptyset)
                                              (distinct E_S1_minus emptyset))
                                         (not (not a!57)))))
                         (a!61 (not (and a!51
                                         (and (distinct E_S1_plus emptyset)
                                              (distinct E_S1_minus emptyset))
                                         (not (not a!60)))))
                         (a!63 (not (and a!51
                                         (and (= E_S1_plus emptyset)
                                              (= E_S1_minus emptyset))
                                         (not (not a!62)))))
                         (a!67 (and a!3
                                    (= emptyset
                                       (setunion (setunion emptyset emptyset)
                                                 E_S3_minus))
                                    (= S1_2_plus
                                       (setunion (setunion E_S1_plus E_S2_plus)
                                                 emptyset))
                                    a!4
                                    a!5
                                    (not a!6)
                                    (not a!66)))
                         (a!69 (and a!3
                                    (= emptyset
                                       (setunion (setunion E_S1_minus emptyset)
                                                 E_S3_minus))
                                    (= S1_2_plus
                                       (setunion (setunion emptyset E_S2_plus)
                                                 emptyset))
                                    a!4
                                    a!5
                                    (not a!11)
                                    (not a!66)))
                         (a!71 (and a!3
                                    (= emptyset
                                       (setunion (setunion E_S1_minus emptyset)
                                                 E_S3_minus))
                                    (= S1_2_plus
                                       (setunion (setunion E_S1_plus E_S2_plus)
                                                 emptyset))
                                    a!4
                                    a!5
                                    (not a!14)
                                    (not a!66)))
                         (a!73 (and a!3
                                    (= emptyset
                                       (setunion (setunion emptyset emptyset)
                                                 E_S3_minus))
                                    (= S1_2_plus
                                       (setunion (setunion emptyset E_S2_plus)
                                                 emptyset))
                                    a!4
                                    a!5
                                    (not a!17)
                                    (not a!66)))
                         (a!77 (and a!22
                                    (= emptyset
                                       (setunion (setunion emptyset E_S2_minus)
                                                 E_S3_minus))
                                    (= S1_2_plus
                                       (setunion (setunion E_S1_plus emptyset)
                                                 emptyset))
                                    a!4
                                    a!23
                                    (not a!25)
                                    (not a!76)))
                         (a!79 (and a!22
                                    (= emptyset
                                       (setunion (setunion E_S1_minus
                                                           E_S2_minus)
                                                 E_S3_minus))
                                    (= S1_2_plus
                                       (setunion (setunion emptyset emptyset)
                                                 emptyset))
                                    a!4
                                    a!23
                                    (not a!30)
                                    (not a!76)))
                         (a!81 (and a!22
                                    (= emptyset
                                       (setunion (setunion E_S1_minus
                                                           E_S2_minus)
                                                 E_S3_minus))
                                    (= S1_2_plus
                                       (setunion (setunion E_S1_plus emptyset)
                                                 emptyset))
                                    a!4
                                    a!23
                                    (not a!33)
                                    (not a!76)))
                         (a!83 (and a!22
                                    (= emptyset
                                       (setunion (setunion emptyset E_S2_minus)
                                                 E_S3_minus))
                                    (= S1_2_plus
                                       (setunion (setunion emptyset emptyset)
                                                 emptyset))
                                    a!4
                                    a!23
                                    (not a!17)
                                    (not a!76)))
                         (a!86 (and (and (= E_S2_minus a!39) (= E_S2_plus a!40))
                                    (= emptyset
                                       (setunion (setunion emptyset E_S2_minus)
                                                 E_S3_minus))
                                    (= S1_2_plus
                                       (setunion (setunion E_S1_plus E_S2_plus)
                                                 emptyset))
                                    a!4
                                    (and true
                                         true
                                         a!41
                                         a!42
                                         true
                                         true
                                         true
                                         true)
                                    (not a!25)
                                    (not a!66)))
                         (a!88 (and (and (= E_S2_minus a!39) (= E_S2_plus a!40))
                                    (= emptyset
                                       (setunion (setunion E_S1_minus
                                                           E_S2_minus)
                                                 E_S3_minus))
                                    (= S1_2_plus
                                       (setunion (setunion emptyset E_S2_plus)
                                                 emptyset))
                                    a!4
                                    (and true
                                         true
                                         a!41
                                         a!42
                                         true
                                         true
                                         true
                                         true)
                                    (not a!30)
                                    (not a!66)))
                         (a!90 (and (and (= E_S2_minus a!39) (= E_S2_plus a!40))
                                    (= emptyset
                                       (setunion (setunion E_S1_minus
                                                           E_S2_minus)
                                                 E_S3_minus))
                                    (= S1_2_plus
                                       (setunion (setunion E_S1_plus E_S2_plus)
                                                 emptyset))
                                    a!4
                                    (and true
                                         true
                                         a!41
                                         a!42
                                         true
                                         true
                                         true
                                         true)
                                    (not a!33)
                                    (not a!66)))
                         (a!92 (and (and (= E_S2_minus a!39) (= E_S2_plus a!40))
                                    (= emptyset
                                       (setunion (setunion emptyset E_S2_minus)
                                                 E_S3_minus))
                                    (= S1_2_plus
                                       (setunion (setunion emptyset E_S2_plus)
                                                 emptyset))
                                    a!4
                                    (and true
                                         true
                                         a!41
                                         a!42
                                         true
                                         true
                                         true
                                         true)
                                    (not a!17)
                                    (not a!66)))
                         (a!97 (not (and a!94
                                         (and (distinct E_S1_plus emptyset)
                                              (= E_S1_minus emptyset))
                                         (not (not a!96)))))
                         (a!99 (not (and a!94
                                         (and (= E_S1_plus emptyset)
                                              (distinct E_S1_minus emptyset))
                                         (not (not a!98)))))
                         (a!101 (not (and a!94
                                          (and (distinct E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!100)))))
                         (a!103 (not (and a!94
                                          (and (= E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!102)))))
                         (a!106 (and a!3
                                     (= emptyset
                                        (setunion (setunion emptyset emptyset)
                                                  E_S3_minus))
                                     (= S1_2_plus
                                        (setunion (setunion E_S1_plus E_S2_plus)
                                                  E_S3_plus))
                                     a!4
                                     a!5
                                     (not a!6)
                                     (not a!105)))
                         (a!108 (and a!3
                                     (= emptyset
                                        (setunion (setunion E_S1_minus emptyset)
                                                  E_S3_minus))
                                     (= S1_2_plus
                                        (setunion (setunion emptyset E_S2_plus)
                                                  E_S3_plus))
                                     a!4
                                     a!5
                                     (not a!11)
                                     (not a!105)))
                         (a!110 (and a!3
                                     (= emptyset
                                        (setunion (setunion E_S1_minus emptyset)
                                                  E_S3_minus))
                                     (= S1_2_plus
                                        (setunion (setunion E_S1_plus E_S2_plus)
                                                  E_S3_plus))
                                     a!4
                                     a!5
                                     (not a!14)
                                     (not a!105)))
                         (a!112 (and a!3
                                     (= emptyset
                                        (setunion (setunion emptyset emptyset)
                                                  E_S3_minus))
                                     (= S1_2_plus
                                        (setunion (setunion emptyset E_S2_plus)
                                                  E_S3_plus))
                                     a!4
                                     a!5
                                     (not a!17)
                                     (not a!105)))
                         (a!116 (and a!22
                                     (= emptyset
                                        (setunion (setunion emptyset E_S2_minus)
                                                  E_S3_minus))
                                     (= S1_2_plus
                                        (setunion (setunion E_S1_plus emptyset)
                                                  E_S3_plus))
                                     a!4
                                     a!23
                                     (not a!25)
                                     (not a!115)))
                         (a!118 (and a!22
                                     (= emptyset
                                        (setunion (setunion E_S1_minus
                                                            E_S2_minus)
                                                  E_S3_minus))
                                     (= S1_2_plus
                                        (setunion (setunion emptyset emptyset)
                                                  E_S3_plus))
                                     a!4
                                     a!23
                                     (not a!30)
                                     (not a!115)))
                         (a!120 (and a!22
                                     (= emptyset
                                        (setunion (setunion E_S1_minus
                                                            E_S2_minus)
                                                  E_S3_minus))
                                     (= S1_2_plus
                                        (setunion (setunion E_S1_plus emptyset)
                                                  E_S3_plus))
                                     a!4
                                     a!23
                                     (not a!33)
                                     (not a!115)))
                         (a!122 (and a!22
                                     (= emptyset
                                        (setunion (setunion emptyset E_S2_minus)
                                                  E_S3_minus))
                                     (= S1_2_plus
                                        (setunion (setunion emptyset emptyset)
                                                  E_S3_plus))
                                     a!4
                                     a!23
                                     (not a!17)
                                     (not a!115)))
                         (a!125 (and (and (= E_S2_minus a!39)
                                          (= E_S2_plus a!40))
                                     (= emptyset
                                        (setunion (setunion emptyset E_S2_minus)
                                                  E_S3_minus))
                                     (= S1_2_plus
                                        (setunion (setunion E_S1_plus E_S2_plus)
                                                  E_S3_plus))
                                     a!4
                                     (and true
                                          true
                                          a!41
                                          a!42
                                          true
                                          true
                                          true
                                          true)
                                     (not a!25)
                                     (not a!105)))
                         (a!127 (and (and (= E_S2_minus a!39)
                                          (= E_S2_plus a!40))
                                     (= emptyset
                                        (setunion (setunion E_S1_minus
                                                            E_S2_minus)
                                                  E_S3_minus))
                                     (= S1_2_plus
                                        (setunion (setunion emptyset E_S2_plus)
                                                  E_S3_plus))
                                     a!4
                                     (and true
                                          true
                                          a!41
                                          a!42
                                          true
                                          true
                                          true
                                          true)
                                     (not a!30)
                                     (not a!105)))
                         (a!129 (and (and (= E_S2_minus a!39)
                                          (= E_S2_plus a!40))
                                     (= emptyset
                                        (setunion (setunion E_S1_minus
                                                            E_S2_minus)
                                                  E_S3_minus))
                                     (= S1_2_plus
                                        (setunion (setunion E_S1_plus E_S2_plus)
                                                  E_S3_plus))
                                     a!4
                                     (and true
                                          true
                                          a!41
                                          a!42
                                          true
                                          true
                                          true
                                          true)
                                     (not a!33)
                                     (not a!105)))
                         (a!131 (and (and (= E_S2_minus a!39)
                                          (= E_S2_plus a!40))
                                     (= emptyset
                                        (setunion (setunion emptyset E_S2_minus)
                                                  E_S3_minus))
                                     (= S1_2_plus
                                        (setunion (setunion emptyset E_S2_plus)
                                                  E_S3_plus))
                                     a!4
                                     (and true
                                          true
                                          a!41
                                          a!42
                                          true
                                          true
                                          true
                                          true)
                                     (not a!17)
                                     (not a!105)))
                         (a!136 (not (and a!133
                                          (and (distinct E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!135)))))
                         (a!138 (not (and a!133
                                          (and (= E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!137)))))
                         (a!140 (not (and a!133
                                          (and (distinct E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!139)))))
                         (a!142 (not (and a!133
                                          (and (= E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!141)))))
                         (a!144 (and a!3
                                     (= emptyset
                                        (setunion (setunion emptyset emptyset)
                                                  emptyset))
                                     (= S1_2_plus
                                        (setunion (setunion E_S1_plus E_S2_plus)
                                                  emptyset))
                                     a!4
                                     a!5
                                     (not a!6)
                                     (not a!17)))
                         (a!146 (and a!3
                                     (= emptyset
                                        (setunion (setunion E_S1_minus emptyset)
                                                  emptyset))
                                     (= S1_2_plus
                                        (setunion (setunion emptyset E_S2_plus)
                                                  emptyset))
                                     a!4
                                     a!5
                                     (not a!11)
                                     (not a!17)))
                         (a!148 (and a!3
                                     (= emptyset
                                        (setunion (setunion E_S1_minus emptyset)
                                                  emptyset))
                                     (= S1_2_plus
                                        (setunion (setunion E_S1_plus E_S2_plus)
                                                  emptyset))
                                     a!4
                                     a!5
                                     (not a!14)
                                     (not a!17)))
                         (a!150 (and a!3
                                     (= emptyset
                                        (setunion (setunion emptyset emptyset)
                                                  emptyset))
                                     (= S1_2_plus
                                        (setunion (setunion emptyset E_S2_plus)
                                                  emptyset))
                                     a!4
                                     a!5
                                     (not a!17)
                                     (not a!17)))
                         (a!153 (and a!22
                                     (= emptyset
                                        (setunion (setunion emptyset E_S2_minus)
                                                  emptyset))
                                     (= S1_2_plus
                                        (setunion (setunion E_S1_plus emptyset)
                                                  emptyset))
                                     a!4
                                     a!23
                                     (not a!25)
                                     (not a!17)))
                         (a!155 (and a!22
                                     (= emptyset
                                        (setunion (setunion E_S1_minus
                                                            E_S2_minus)
                                                  emptyset))
                                     (= S1_2_plus
                                        (setunion (setunion emptyset emptyset)
                                                  emptyset))
                                     a!4
                                     a!23
                                     (not a!30)
                                     (not a!17)))
                         (a!157 (and a!22
                                     (= emptyset
                                        (setunion (setunion E_S1_minus
                                                            E_S2_minus)
                                                  emptyset))
                                     (= S1_2_plus
                                        (setunion (setunion E_S1_plus emptyset)
                                                  emptyset))
                                     a!4
                                     a!23
                                     (not a!33)
                                     (not a!17)))
                         (a!159 (and a!22
                                     (= emptyset
                                        (setunion (setunion emptyset E_S2_minus)
                                                  emptyset))
                                     (= S1_2_plus
                                        (setunion (setunion emptyset emptyset)
                                                  emptyset))
                                     a!4
                                     a!23
                                     (not a!17)
                                     (not a!17)))
                         (a!162 (and (and (= E_S2_minus a!39)
                                          (= E_S2_plus a!40))
                                     (= emptyset
                                        (setunion (setunion emptyset E_S2_minus)
                                                  emptyset))
                                     (= S1_2_plus
                                        (setunion (setunion E_S1_plus E_S2_plus)
                                                  emptyset))
                                     a!4
                                     (and true
                                          true
                                          a!41
                                          a!42
                                          true
                                          true
                                          true
                                          true)
                                     (not a!25)
                                     (not a!17)))
                         (a!165 (not (and a!161
                                          (and (= E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!164)))))
                         (a!166 (and (and (= E_S2_minus a!39)
                                          (= E_S2_plus a!40))
                                     (= emptyset
                                        (setunion (setunion E_S1_minus
                                                            E_S2_minus)
                                                  emptyset))
                                     (= S1_2_plus
                                        (setunion (setunion E_S1_plus E_S2_plus)
                                                  emptyset))
                                     a!4
                                     (and true
                                          true
                                          a!41
                                          a!42
                                          true
                                          true
                                          true
                                          true)
                                     (not a!33)
                                     (not a!17)))
                         (a!169 (not (and a!161
                                          (and (= E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!168)))))
                         (a!172 (not (and a!170
                                          (and (distinct E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!171)))))
                         (a!174 (not (and a!170
                                          (and (= E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!173)))))
                         (a!176 (not (and a!170
                                          (and (distinct E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!175)))))
                         (a!178 (not (and a!170
                                          (and (= E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!177))))))
                   (let ((a!9 (not (and a!1
                                        (and (distinct E_S1_plus emptyset)
                                             (= E_S1_minus emptyset))
                                        (not (not a!8)))))
                         (a!13 (not (and a!1
                                         (and (= E_S1_plus emptyset)
                                              (distinct E_S1_minus emptyset))
                                         (not (not a!12)))))
                         (a!16 (not (and a!1
                                         (and (distinct E_S1_plus emptyset)
                                              (distinct E_S1_minus emptyset))
                                         (not (not a!15)))))
                         (a!19 (not (and a!1
                                         (and (= E_S1_plus emptyset)
                                              (= E_S1_minus emptyset))
                                         (not (not a!18)))))
                         (a!29 (not (and a!20
                                         (and (distinct E_S1_plus emptyset)
                                              (= E_S1_minus emptyset))
                                         (not (not a!28)))))
                         (a!32 (not (and a!20
                                         (and (= E_S1_plus emptyset)
                                              (distinct E_S1_minus emptyset))
                                         (not (not a!31)))))
                         (a!35 (not (and a!20
                                         (and (distinct E_S1_plus emptyset)
                                              (distinct E_S1_minus emptyset))
                                         (not (not a!34)))))
                         (a!37 (not (and a!20
                                         (and (= E_S1_plus emptyset)
                                              (= E_S1_minus emptyset))
                                         (not (not a!36)))))
                         (a!44 (not (and a!38
                                         (and (distinct E_S1_plus emptyset)
                                              (= E_S1_minus emptyset))
                                         (not (not a!43)))))
                         (a!48 (not (and a!38
                                         (and (distinct E_S1_plus emptyset)
                                              (distinct E_S1_minus emptyset))
                                         (not (not a!47)))))
                         (a!68 (not (and a!64
                                         (and (distinct E_S1_plus emptyset)
                                              (= E_S1_minus emptyset))
                                         (not (not a!67)))))
                         (a!70 (not (and a!64
                                         (and (= E_S1_plus emptyset)
                                              (distinct E_S1_minus emptyset))
                                         (not (not a!69)))))
                         (a!72 (not (and a!64
                                         (and (distinct E_S1_plus emptyset)
                                              (distinct E_S1_minus emptyset))
                                         (not (not a!71)))))
                         (a!74 (not (and a!64
                                         (and (= E_S1_plus emptyset)
                                              (= E_S1_minus emptyset))
                                         (not (not a!73)))))
                         (a!78 (not (and a!75
                                         (and (distinct E_S1_plus emptyset)
                                              (= E_S1_minus emptyset))
                                         (not (not a!77)))))
                         (a!80 (not (and a!75
                                         (and (= E_S1_plus emptyset)
                                              (distinct E_S1_minus emptyset))
                                         (not (not a!79)))))
                         (a!82 (not (and a!75
                                         (and (distinct E_S1_plus emptyset)
                                              (distinct E_S1_minus emptyset))
                                         (not (not a!81)))))
                         (a!84 (not (and a!75
                                         (and (= E_S1_plus emptyset)
                                              (= E_S1_minus emptyset))
                                         (not (not a!83)))))
                         (a!87 (not (and a!85
                                         (and (distinct E_S1_plus emptyset)
                                              (= E_S1_minus emptyset))
                                         (not (not a!86)))))
                         (a!89 (not (and a!85
                                         (and (= E_S1_plus emptyset)
                                              (distinct E_S1_minus emptyset))
                                         (not (not a!88)))))
                         (a!91 (not (and a!85
                                         (and (distinct E_S1_plus emptyset)
                                              (distinct E_S1_minus emptyset))
                                         (not (not a!90)))))
                         (a!93 (not (and a!85
                                         (and (= E_S1_plus emptyset)
                                              (= E_S1_minus emptyset))
                                         (not (not a!92)))))
                         (a!107 (not (and a!104
                                          (and (distinct E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!106)))))
                         (a!109 (not (and a!104
                                          (and (= E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!108)))))
                         (a!111 (not (and a!104
                                          (and (distinct E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!110)))))
                         (a!113 (not (and a!104
                                          (and (= E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!112)))))
                         (a!117 (not (and a!114
                                          (and (distinct E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!116)))))
                         (a!119 (not (and a!114
                                          (and (= E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!118)))))
                         (a!121 (not (and a!114
                                          (and (distinct E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!120)))))
                         (a!123 (not (and a!114
                                          (and (= E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!122)))))
                         (a!126 (not (and a!124
                                          (and (distinct E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!125)))))
                         (a!128 (not (and a!124
                                          (and (= E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!127)))))
                         (a!130 (not (and a!124
                                          (and (distinct E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!129)))))
                         (a!132 (not (and a!124
                                          (and (= E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!131)))))
                         (a!145 (not (and a!143
                                          (and (distinct E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!144)))))
                         (a!147 (not (and a!143
                                          (and (= E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!146)))))
                         (a!149 (not (and a!143
                                          (and (distinct E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!148)))))
                         (a!151 (not (and a!143
                                          (and (= E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!150)))))
                         (a!154 (not (and a!152
                                          (and (distinct E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!153)))))
                         (a!156 (not (and a!152
                                          (and (= E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!155)))))
                         (a!158 (not (and a!152
                                          (and (distinct E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!157)))))
                         (a!160 (not (and a!152
                                          (and (= E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!159)))))
                         (a!163 (not (and a!161
                                          (and (distinct E_S1_plus emptyset)
                                               (= E_S1_minus emptyset))
                                          (not (not a!162)))))
                         (a!167 (not (and a!161
                                          (and (distinct E_S1_plus emptyset)
                                               (distinct E_S1_minus emptyset))
                                          (not (not a!166))))))
                     (and a!9
                          a!13
                          a!16
                          a!19
                          a!29
                          a!32
                          a!35
                          a!37
                          a!44
                          a!46
                          a!48
                          a!50
                          a!55
                          a!58
                          a!61
                          a!63
                          a!68
                          a!70
                          a!72
                          a!74
                          a!78
                          a!80
                          a!82
                          a!84
                          a!87
                          a!89
                          a!91
                          a!93
                          a!97
                          a!99
                          a!101
                          a!103
                          a!107
                          a!109
                          a!111
                          a!113
                          a!117
                          a!119
                          a!121
                          a!123
                          a!126
                          a!128
                          a!130
                          a!132
                          a!136
                          a!138
                          a!140
                          a!142
                          a!145
                          a!147
                          a!149
                          a!151
                          a!154
                          a!156
                          a!158
                          a!160
                          a!163
                          a!165
                          a!167
                          a!169
                          a!172
                          a!174
                          a!176
                          a!178)))))))))
(let ((a!5 (or a!3
               false
               (and (>= (min S1_plus) 0) (>= (max emptyset) 10))
               (and (>= (min S1_plus) 1) (>= (max emptyset) 9))
               (and (>= (min S1_plus) 2) (>= (max emptyset) 8))
               (and (>= (min S1_plus) 3) (>= (max emptyset) 7))
               (and (>= (min S1_plus) 4) (>= (max emptyset) 6))
               (and (>= (min S1_plus) 5) (>= (max emptyset) 5))
               (and (>= (min S1_plus) 6) (>= (max emptyset) 4))
               (and (>= (min S1_plus) 7) (>= (max emptyset) 3))
               (and (>= (min S1_plus) 8) (>= (max emptyset) 2))
               (and (>= (min S1_plus) 9) (>= (max emptyset) 1))
               (and (>= (min S1_plus) 10) (>= (max emptyset) 0))
               a!4))
      (a!11 (or a!9
                false
                (and (>= (min S1_1_plus) 0) (>= (max emptyset) 10))
                (and (>= (min S1_1_plus) 1) (>= (max emptyset) 9))
                (and (>= (min S1_1_plus) 2) (>= (max emptyset) 8))
                (and (>= (min S1_1_plus) 3) (>= (max emptyset) 7))
                (and (>= (min S1_1_plus) 4) (>= (max emptyset) 6))
                (and (>= (min S1_1_plus) 5) (>= (max emptyset) 5))
                (and (>= (min S1_1_plus) 6) (>= (max emptyset) 4))
                (and (>= (min S1_1_plus) 7) (>= (max emptyset) 3))
                (and (>= (min S1_1_plus) 8) (>= (max emptyset) 2))
                (and (>= (min S1_1_plus) 9) (>= (max emptyset) 1))
                (and (>= (min S1_1_plus) 10) (>= (max emptyset) 0))
                a!10)))
(let ((a!6 (and (and |[E,0]| (>= E_plus 1))
                (= emptyset (setunion emptyset (setunion emptyset emptyset)))
                (= S1_plus a!2)
                a!5
                (<= (max S1_plus) (+ (min S1_plus) 100))))
      (a!13 (and (and |[E,0]| (>= E_plus 1))
                 (= emptyset (setunion emptyset (setunion emptyset emptyset)))
                 (= S1_plus a!7)
                 a!5
                 (<= (max S1_plus) (+ (min S1_plus) 100))
                 (= emptyset (setunion emptyset (setunion emptyset emptyset)))
                 (= S1_1_plus a!8)
                 a!11
                 (<= (max S1_1_plus) (+ (min S1_1_plus) 100))
                 (not a!12))))
  (and (= (min S2_plus) (+ (min S1_plus) 7))
       (not (and a!1 (not a!6) (not a!13)))
       true
       (= S1_minus emptyset)
       (distinct S1_plus emptyset)
       (= S2_minus emptyset)
       (distinct S2_plus emptyset)
       (= S1_1_minus emptyset)
       (distinct S1_1_plus emptyset)
       (= S1_2_minus emptyset)
       (distinct S1_2_plus emptyset)))))
