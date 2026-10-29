---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

vars == <<hr>>

Hours == 1..12

TypeOK == hr \in Hours

Init == hr \in Hours

(* Stepwise "increment-or-wrap" transition *)
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

(* Alternative concise modular-arithmetic transition *)
HCnxtMod == hr' = (hr % 12) + 1

Next == HCnxt

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Alternative specification using the modular formulation *)
SpecMod == Init /\ [][HCnxtMod]_vars /\ WF_vars(HCnxtMod)

---------------------------------------------------------------------------
(* Safety *)

Inv == TypeOK

Safety == []TypeOK

(* Equivalence of the two transition formulations, as a state predicate:
   for the current hour, both formulations compute the same successor. *)
NextHour(h) == IF h # 12 THEN h + 1 ELSE 1
NextHourMod(h) == (h % 12) + 1

EquivInv == NextHour(hr) = NextHourMod(hr)

(* Static equivalence over the whole dial *)
EquivAll == \A h \in Hours : NextHour(h) = NextHourMod(h)

(* Action-level equivalence: every step taken satisfies both formulations *)
StepEquiv == [][HCnxt <=> HCnxtMod]_vars

(* Every non-stuttering step of Spec is a step of the modular formulation *)
StepRefinesMod == [][HCnxtMod]_vars

(* Next is always enabled: the clock never gets stuck *)
NeverStuck == [](ENABLED Next)

---------------------------------------------------------------------------
(* Liveness *)

(* The clock ticks infinitely often *)
Progress == []<>(<<Next>>_vars)

(* Every hour is visited infinitely often *)
VisitsAllHours == \A h \in Hours : []<>(hr = h)

(* The clock always eventually reaches its subsequent hour *)
EventuallyNextHour == \A h \in Hours : (hr = h) ~> (hr = NextHour(h))

---------------------------------------------------------------------------
(* Theorems *)

THEOREM TypeCorrect == Spec => []TypeOK

THEOREM EquivalenceStatic == EquivAll

THEOREM EquivalenceSpec == Spec <=> SpecMod

THEOREM SpecRefinesMod == Spec => StepRefinesMod

THEOREM SpecLiveness == Spec => (Progress /\ VisitsAllHours /\ EventuallyNextHour)

=============================================================================