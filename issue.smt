; z3 issue.smt
(assert (not (forall ((n Int))
                     (exists ((m Int)) ; use m for n'
                             (forall ((n0 Int) (n4 Int))
                                     (=> (and (= n4 n)
                                              (>= n 0)
                                              (>= m 0)
                                              (not (and (= n0 0)
                                                        (= n0 n))))
                                         (= n4 (+ m 1))))))))
(check-sat)
