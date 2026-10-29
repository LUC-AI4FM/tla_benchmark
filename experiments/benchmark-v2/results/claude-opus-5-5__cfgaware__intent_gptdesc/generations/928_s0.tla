---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

vars == <<hr>>

Hours == 1..12

(* Initial condition: any valid hour on the dial *)
HCini == hr \in Hours

(* Stepwise "increment-or-wrap" transition *)
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

(* Alternative concise transition using modular arithmetic *)
HCnxt2 == hr' = (hr % 12) + 1

(* Main specification: deterministic advance with weak fairness for progress *)
HC == HCini /\ [][HCnxt]_hr /\ WF_hr(HCnxt)

(* Alternative specification using the modular-arithmetic transition *)
HC2 == HCini /\ [][HCnxt2]_hr /\ WF_hr(HCnxt2)

-----------------------------------------------------------------------------
(* Safety: the clock always shows a valid hour *)
TypeOK == hr \in Hours

Safety == []TypeOK

(* Equivalence of the two transition formulations, as a state predicate:
   in every reachable state, both formulations compute the same next hour *)
NextEquiv == (IF hr # 12 THEN hr + 1 ELSE 1) = (hr % 12) + 1

(* Equivalence as an action property: every HCnxt step is an HCnxt2 step and vice versa *)
ActionEquiv == [][HCnxt <=> HCnxt2]_hr

(* Liveness: the clock never gets stuck; every hour is visited infinitely often *)
Progress == \A h \in Hours : []<>(hr = h)

(* Liveness: from any hour, the subsequent hour is eventually reached *)
NextHourEventually ==
    \A h \in Hours : (hr = h) ~> (hr = (h % 12) + 1)

(* The clock always eventually changes value *)
NeverStuck == []<><<HCnxt>>_hr

(* Theorems relating the two formulations *)
THEOREM HC => Safety
THEOREM HC => []NextEquiv
THEOREM HC => HC2
THEOREM HC2 => HC
THEOREM HC => Progress
=============================================================================