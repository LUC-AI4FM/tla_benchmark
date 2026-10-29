---- MODULE HourClock ----
EXTENDS Naturals

VARIABLE hr

vars == <<hr>>

(* Valid-hour predicate; also the initial-state predicate *)
HCini == hr \in (1 .. 12)

(* Atomic, deterministic step: increment, or wrap from 12 to 1 *)
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

(* Complete specification *)
HC == HCini /\ [][HCnxt]_hr

(* Fair specification: the clock keeps advancing forever *)
FairHC == HC /\ WF_hr(HCnxt)

(* Safety: the hour is always within 1..12 *)
TypeOK == hr \in (1 .. 12)

(* Safety: every transition follows the increment-or-wrap rule *)
TransitionCorrect ==
    [][ \/ (hr < 12 /\ hr' = hr + 1)
        \/ (hr = 12 /\ hr' = 1) ]_hr

(* No deadlock: a next transition is always enabled *)
NoDeadlock == [](ENABLED HCnxt)

(* Liveness: under fairness, the clock advances forever *)
AlwaysAdvances == []<><<HCnxt>>_hr

(* Proof obligation: initial validity implies the invariant holds globally *)
THEOREM HC => []HCini

THEOREM HC => TransitionCorrect

THEOREM HC => NoDeadlock

THEOREM FairHC => AlwaysAdvances
====