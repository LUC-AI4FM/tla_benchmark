---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

vars == << hr >>

Hours == 1..12

-----------------------------------------------------------------------------
(* Initial condition: the hour is any valid 12-hour value *)
Init == hr \in Hours

(* Step relation: advance by one hour, wrapping from 12 back to 1 *)
Tick == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Next == Tick

(* Weak fairness on Tick is enough for liveness, because Tick is always enabled *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Alternative specification using strong fairness. It is equivalent here *)
FairSpec == Init /\ [][Next]_vars /\ SF_vars(Next)

-----------------------------------------------------------------------------
(* Safety: the hour always lies in 1..12 *)
TypeOK == hr \in Hours

(* Functional correctness: every step advances the hour by one, modulo 12 *)
StepIsModIncrement == [][hr' = (hr % 12) + 1]_vars

(* No deadlock: the Tick action is enabled in every state *)
AlwaysEnabled == [](ENABLED Tick)

(* Liveness: the clock takes real steps infinitely often *)
InfinitelyManySteps == []<><<Next>>_vars

(* Eventual recurrence: every hour value occurs infinitely often *)
AllHoursRecur == \A h \in Hours : []<>(hr = h)

-----------------------------------------------------------------------------
(* Initialization establishes the invariant *)
THEOREM InitEstablishesInv == Init => TypeOK

(* Every transition preserves the invariant *)
THEOREM NextPreservesInv == TypeOK /\ [Next]_vars => TypeOK'

(* The invariant holds globally *)
THEOREM SpecSafety == Spec => []TypeOK

(* The step relation implements the modulo-12 increment *)
THEOREM NextIsModIncrement == TypeOK /\ Next => hr' = (hr % 12) + 1

THEOREM SpecFunctional == Spec => StepIsModIncrement

THEOREM SpecNoDeadlock == Spec => AlwaysEnabled

(* Under fair execution, steps continue forever and all 12 hours recur *)
THEOREM SpecLiveness == Spec => (InfinitelyManySteps /\ AllHoursRecur)

THEOREM FairSpecLiveness == FairSpec => (InfinitelyManySteps /\ AllHoursRecur)

=============================================================================