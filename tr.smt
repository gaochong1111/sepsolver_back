(let ((a!1 (setunion ?S1 (setunion (set (min ?S)) (set (max ?S)))))
      (a!2 (and true (>= (max ?S) (+ (min ?S) 5))))
      (a!3 (and true (<= (min ?S1) (+ (max ?S1) 0)))))
(let ((a!4 (and (= ?S a!1)
                true
                (= (min ?S1) (+ (min ?S) 2))
                a!2
                true
                (>= (max ?S1) (+ (min ?S) 2))
                true
                (>= (max ?S) (+ (min ?S1) 3))
                a!3
                true
                (= (max ?S) (+ (max ?S1) 3)))))
  (not (and (not (= ?S ?S1))
            (not a!4)
            (forall ((E_S1 SetInt) (E_S2 SetInt) (E_S3 SetInt) (E_S4 SetInt))
              (let ((a!1 (setunion E_S1
                                   (setunion (set (min ?S)) (set (max ?S)))))
                    (a!2 (setunion ?S1
                                   (setunion (set (min E_S2)) (set (max E_S2)))))
                    (a!3 (not (and (not (= E_S3 emptyset))
                                   (>= (max E_S3) (min E_S2)))))
                    (a!4 (not (and (not (= E_S4 emptyset))
                                   (>= (max E_S2) (min E_S4)))))
                    (a!5 (and true (>= (max ?S) (+ (min ?S) 5))))
                    (a!6 (and true (<= (min ?S1) (+ (max ?S1) 0))))
                    (a!7 (= (* 3 (- (min ?S1) (min ?S)))
                            (* 2 (- (max ?S) (max ?S1))))))
              (let ((a!8 (and (= ?S a!1)
                              (= E_S1 (setunion (setunion E_S2 E_S3) E_S4))
                              (= E_S2 a!2)
                              a!3
                              a!4
                              true
                              (= (min ?S1) (+ (min E_S2) 2))
                              true
                              (= (min E_S1) (+ (min ?S) 2))
                              a!5
                              true
                              (>= (max E_S2) (+ (min E_S2) 5))
                              true
                              (>= (max ?S1) (+ (min E_S2) 2))
                              true
                              (>= (max E_S1) (+ (min ?S) 2))
                              true
                              (>= (max E_S2) (+ (min ?S1) 3))
                              true
                              (>= (max ?S) (+ (min E_S1) 3))
                              a!6
                              true
                              (<= (min E_S1) (+ (max E_S1) 0))
                              true
                              (= (max E_S2) (+ (max ?S1) 3))
                              true
                              (= (max ?S) (+ (max E_S1) 3))
                              (forall ((x Int) (y Int))
                                (let ((a!1 (subset (set x)
                                                   (setunion E_S3
                                                             (set (min E_S2)))))
                                      (a!2 (subset (set y)
                                                   (setunion E_S3
                                                             (set (min E_S2)))))
                                      (a!3 (not (and true (= y (+ x 2))))))
                                (let ((a!4 (and a!1
                                                a!2
                                                (>= y (+ x 1))
                                                (forall ((z Int))
                                                  (let ((a!1 (subset (set z)
                                                                     (setunion E_S3
                                                                               (set (min E_S2)))))
                                                        (a!2 (and (>= z (+ x 1))
                                                                  (>= y (+ z 1)))))
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
                                      (a!3 (not (and true (= y (+ x 3))))))
                                (let ((a!4 (and a!1
                                                a!2
                                                (>= y (+ x 1))
                                                (forall ((z Int))
                                                  (let ((a!1 (subset (set z)
                                                                     (setunion E_S4
                                                                               (set (max E_S2)))))
                                                        (a!2 (and (>= z (+ x 1))
                                                                  (>= y (+ z 1)))))
                                                    (not (and a!1 a!2))))
                                                a!3)))
                                  (not a!4))))
                              a!7)))
                (not a!8))))))))
