------------------------------- MODULE HourClock -------------------------------
(***************************************************************************)
(* A simple 12-hour clock.                                                 *)
(*                                                                         *)
(* The state is one integer variable hr, the displayed hour, which must     *)
(* stay in 1..12. Two atomic actions can occur nondeterministically and     *)
(* repeatedly:                                                              *)
(*   Tick   : advance the hour by one, wrapping from 12 back to 1.          *)
(*   Set(h) : assign the clock to any valid hour h in 1..12.                *)
(* Time is modeled as a discrete sequence of these steps.                   *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT InitHours          \* the hours the clock may start at
ASSUME InitHoursValid == InitHours \subseteq 1..12 /\ InitHours # {}

VARIABLE hr

vars == <<hr>>

Hours == 1..12

-----------------------------------------------------------------------------
(* Next-hour function with wrap-around from 12 to 1.                       *)
NextHour(h) == IF h = 12 THEN 1 ELSE h + 1

(* The initial hour is chosen nondeterministically among InitHours.        *)
(* To start from any valid hour, set InitHours <- 1..12.                   *)
Init == hr \in InitHours

(* Automatic tick: advance by one hour.                                    *)
Tick == hr' = NextHour(hr)

(* Explicit set: assign the clock to any valid hour.                       *)
Set(h) == /\ h \in Hours
          /\ hr' = h

SetAny == \E h \in Hours : Set(h)

Next == Tick \/ SetAny

(* Base specification: only safety, no fairness.                           *)
Spec == Init /\ [][Next]_vars

(* Fair specification: the clock keeps ticking. Weak fairness on Tick      *)
(* guarantees that time advances infinitely often.                         *)
FairSpec == Spec /\ WF_vars(Tick)

(* Tick-only specification, used to show that every hour is eventually    *)
(* reached using ticks alone.                                               *)
TickSpec == Init /\ [][Tick]_vars /\ WF_vars(Tick)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

(* Type correctness and (1) Invariance: the hour is always in 1..12.       *)
TypeOK == hr \in Hours

HourInRange == 1 <= hr /\ hr <= 12

(* (3) Wrap-around correctness: a tick at hour 12 yields hour 1.           *)
WrapAround == [][(hr = 12 /\ Tick) => hr' = 1]_vars

(* Ticks advance exactly by one in all other cases.                        *)
TickIncrement == [][(hr # 12 /\ Tick) => hr' = hr + 1]_vars

(* Every step of the system keeps the hour valid.                          *)
StepsPreserveRange == [][hr' \in Hours]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* (2) Progress / strong connectivity                                      *)
(***************************************************************************)

(* From every reachable state, every target hour is reachable in one step  *)
(* through Set, so the state graph over the 12 hours is strongly connected.*)
SetAlwaysEnabled == \A h \in Hours : ENABLED Set(h)

(* Strong connectivity via ticks alone: from any hour, any target hour can *)
(* be reached after (target - hr) mod 12 ticks.                            *)
RECURSIVE TickN(_, _)
TickN(h, n) == IF n = 0 THEN h ELSE TickN(NextHour(h), n - 1)

TicksNeeded(from, to) == (to + 12 - from) % 12

StronglyConnected ==
    \A h \in Hours : TickN(hr, TicksNeeded(hr, h)) = h

(* Tick is always enabled, so under FairSpec the clock ticks infinitely    *)
(* often.                                                                   *)
TickAlwaysEnabled == ENABLED Tick

KeepsTicking == []<><<Tick>>_vars                 \* check under FairSpec

(* Under TickSpec, every hour is reached infinitely often.                 *)
EveryHourReached == \A h \in Hours : []<>(hr = h)  \* check under TickSpec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Theorems                                                                *)
(***************************************************************************)
THEOREM Spec => []TypeOK
THEOREM Spec => []HourInRange
THEOREM Spec => WrapAround
THEOREM Spec => TickIncrement
THEOREM Spec => StepsPreserveRange
THEOREM Spec => []SetAlwaysEnabled
THEOREM Spec => []StronglyConnected
THEOREM Spec => []TickAlwaysEnabled
THEOREM FairSpec => KeepsTicking
THEOREM TickSpec => EveryHourReached
=============================================================================