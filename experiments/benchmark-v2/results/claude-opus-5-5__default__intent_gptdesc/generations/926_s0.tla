---------------------------- MODULE HourClock12 ----------------------------
(***************************************************************************)
(* A simple 12-hour clock counter modelling an hours display that cycles  *)
(* through the values 1..12. A single deterministic step advances the     *)
(* displayed hour by one, wrapping from 12 back to 1.                     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT MaxHour            \* Number of hours on the dial (12 for this clock)

ASSUME MaxHourAssumption == MaxHour = 12

VARIABLE hr                 \* The currently displayed hour

vars == << hr >>

Hours == 1..MaxHour

(***************************************************************************)
(* Modulo-12 increment: the successor of an hour on the dial.             *)
(***************************************************************************)
NextHour(h) == (h % MaxHour) + 1

(***************************************************************************)
(* Static (constant-level) facts about the step function.                 *)
(***************************************************************************)

\* The successor of every legal hour is itself a legal hour.
NextHourInRange == \A h \in Hours : NextHour(h) \in Hours

\* Correct wraparound: 12 -> 1, and h -> h+1 for h in 1..11.
WraparoundCorrect ==
    /\ NextHour(MaxHour) = 1
    /\ \A h \in 1..(MaxHour - 1) : NextHour(h) = h + 1

\* Determinism: from every hour there is exactly one successor hour.
StepRel(h, h2) == h2 = NextHour(h)

DeterministicStep ==
    \A h \in Hours :
        \E h2 \in Hours :
            /\ StepRel(h, h2)
            /\ \A h3 \in Hours : StepRel(h, h3) => h3 = h2

ASSUME StaticFacts == NextHourInRange /\ WraparoundCorrect /\ DeterministicStep

(***************************************************************************)
(* Initial state: any hour in 1..12.                                       *)
(***************************************************************************)
Init == hr \in Hours

(***************************************************************************)
(* The single step action: advance the display by one hour (mod 12).      *)
(***************************************************************************)
Tick == hr' = NextHour(hr)

Next == Tick

(***************************************************************************)
(* Specification with weak fairness so the clock keeps ticking.           *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* Type / range invariant: the displayed hour is always an integer in 1..12.
TypeOK == hr \in Hours

RangeInvariant == hr \in Nat /\ 1 <= hr /\ hr <= MaxHour

\* No step can produce a value outside the range.
StepPreservesRange == [][hr \in Hours => hr' \in Hours]_vars

\* Every step taken is exactly the modulo-12 increment (determinism).
StepIsDeterministic == [][hr' = NextHour(hr)]_vars

\* Wraparound semantics as an action property over behaviours.
WraparoundProperty ==
    [][ /\ (hr = MaxHour => hr' = 1)
        /\ (hr \in 1..(MaxHour - 1) => hr' = hr + 1) ]_vars

\* The step action is always enabled (exactly one step exists from every state).
AlwaysEnabled == ENABLED Next

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

\* Every hour value is reached infinitely often.
EveryHourInfinitelyOften == \A h \in Hours : []<>(hr = h)

\* Each hour is eventually reached from any point in the behaviour.
EventuallyEachHour == \A h \in Hours : [](TRUE ~> (hr = h))

\* The clock never stops ticking.
AlwaysProgresses == []<><<Next>>_vars

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []RangeInvariant
THEOREM Spec => []AlwaysEnabled
THEOREM Spec => StepPreservesRange
THEOREM Spec => StepIsDeterministic
THEOREM Spec => WraparoundProperty
THEOREM Spec => EveryHourInfinitelyOften
THEOREM Spec => EventuallyEachHour
THEOREM Spec => AlwaysProgresses
=============================================================================