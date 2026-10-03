------------------------------ MODULE LiveHourClock ------------------------------

EXTENDS HourClock, Integers

VARIABLES hr

(*
 LSpec augments the HourClock spec HC with a weak fairness condition on HCnxt over hr.
*)
LSpec == HC /\ WF_hr(HCnxt)

(*
 Ticking happens infinitely often: the non-stuttering clock step HCnxt occurs infinitely often.
*)
AlwaysTick == []<>(HCnxt)

(*
 Every hour value from 1 through 12 recurs infinitely often.
*)
AllTimes == \A t \in 1..12 : []<>(hr = t)

(*
 The initial-state typing condition (hr in 1..12) remains always true.
*)
TypeInvariance == [](hr \in 1..12)

THEOREM LSpec => AlwaysTick /\ AllTimes /\ TypeInvariance

(*
 A concrete settling property and a counterexample-shaped postcondition:
   - SettleAt1 says the clock eventually stabilizes at 1.
   - CE_SettleAt1 asserts that under LSpec, such settling does not occur.
 These are auxiliary and not required by the configuration.
*)
SettleAt1 == <>[](hr = 1)
CE_SettleAt1 == LSpec /\ ~SettleAt1

===============================================================================