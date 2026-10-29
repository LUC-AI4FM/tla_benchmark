---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

vars == <<hr>>

Hours == 0..11

(* Initial condition: the clock starts at some arbitrary hour in 0..11 *)
HCini == hr \in Hours

(* Normal tick: advance the hour by one, modulo 12 *)
Tick == hr' = (hr + 1) % 12

(* External set operation: replace the current hour with any allowed value *)
SetTo(v) == /\ v \in Hours
            /\ hr' = v

Set == \E v \in Hours : SetTo(v)

(* Each event is a single atomic update of the clock *)
HCnxt == Tick \/ Set

(* Full specification. Weak fairness on Tick keeps ticks from being
   permanently disabled, so the clock always eventually changes. *)
HC == HCini /\ [][HCnxt]_hr /\ WF_hr(Tick)

---------------------------------------------------------------------------
(* Helper: the value reached after n successive ticks from h *)
TickN(h, n) == (h + n) % 12

(* Safety: the clock value is always within 0..11 *)
TypeOK == hr \in Hours

RangeInv == hr \in Hours

(* Deterministic wrap-around: 12 successive ticks return to the start,
   and every intermediate tick yields a distinct hour of the cycle *)
WrapAroundInv ==
    /\ TickN(hr, 12) = hr
    /\ \A i, j \in 0..11 : (i # j) => (TickN(hr, i) # TickN(hr, j))
    /\ {TickN(hr, i) : i \in 0..11} = Hours

(* Tick step correctness, as an action property *)
TickCorrect == [][Tick => hr' = (hr + 1) % 12]_hr

(* Tick at 11 wraps to 0 *)
WrapStep == [][(Tick /\ hr = 11) => hr' = 0]_hr

(* Set consistency: after an external write of v, the clock equals v *)
SetConsistency == [][\A v \in Hours : SetTo(v) => hr' = v]_hr

(* No lost updates under serial execution: in two sequential atomic events,
   the final value is determined by the second event alone *)
SecondTick(h) == (h + 1) % 12

NoLostUpdate ==
    \A h, v1, v2 \in Hours :
        /\ (* set then set: final value is the second written value *)
           LET mid == v1 IN LET fin == v2 IN fin = v2
        /\ (* tick then set: final value is the written value *)
           LET mid == SecondTick(h) IN LET fin == v2 IN fin = v2
        /\ (* set then tick: final value is the tick applied to the written value *)
           LET mid == v1 IN LET fin == SecondTick(mid) IN fin = (v1 + 1) % 12

NoLostUpdateAction == [][\A v \in Hours : SetTo(v) => hr' = v]_hr

(* Every step keeps the clock in range *)
StepInRange == [][hr' \in Hours]_hr

(* Progress: the clock always eventually changes *)
Progress == []<><<HCnxt>>_hr

(* Ticks are never permanently disabled *)
TickAlwaysEnabled == [](ENABLED Tick)

(* Liveness consequence: every hour that is reachable is eventually left *)
EventuallyChanges == \A h \in Hours : [](hr = h => <>(hr # h))

THEOREM HC => []TypeOK
THEOREM HC => []WrapAroundInv
THEOREM HC => SetConsistency
THEOREM HC => Progress
=============================================================================