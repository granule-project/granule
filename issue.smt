; z3 issue.smt
(assert (not (forall ((n Int))
                     (=> (>= n 0)
                         (exists ((m Int)) ; use m for n'
                                 (=> (>= m 0)
                                     (forall ((n0 Int) (n4 Int))
                                             (=> (and (= n4 n)
                                                      (not (and (= n0 0)
                                                                (= n0 n))))
                                                 (= n4 (+ m 1))))))))))
(check-sat)
