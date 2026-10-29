--------------------------- MODULE LiveHourClock ---------------------------
(***************************************************************************)
(* The hour clock of module HourClock, augmented with a liveness           *)
(* requirement.  The HourClock definitions are included inline so that     *)
(* this module parses on its own.                                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC, TLCExt

VARIABLE hr

(***************************************************************************)
(* Definitions inherited from HourClock                                    *)
(***************************************************************************)
HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

(***************************************************************************)
(* Standard names                                                          *)
(***************************************************************************)
Init == HCini

Next == HCnxt

(***************************************************************************)
(* The live hour clock specification: HC plus weak fairness of HCnxt.      *)
(***************************************************************************)
LSpec == HC /\ WF_hr(HCnxt)

Spec == LSpec

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
\* The clock ticks infinitely often.
AlwaysTick == []<><<HCnxt>>_hr

\* Every hour value from 1 through 12 recurs infinitely often.
AllTimes == \A n \in 1 .. 12 : []<>(hr = n)

\* The initial-state typing condition remains always true.
TypeCorrect == []HCini

THEOREM LSpec => AlwaysTick /\ AllTimes /\ TypeCorrect

(***************************************************************************)
(* A settling property that does NOT hold under LSpec: the clock           *)
(* eventually stays at a single hour forever.  Model checking it yields a  *)
(* lasso-shaped counterexample in which the clock cycles through all 12    *)
(* hours.                                                                  *)
(***************************************************************************)
Settle == \E n \in 1 .. 12 : <>[](hr = n)

(***************************************************************************)
(* Postcondition describing the structure of the counterexample to Settle: *)
(* it has exactly 12 distinct states covering every hour 1..12, and        *)
(* exactly 12 transitions, each of which advances the clock by one hour    *)
(* (wrapping from 12 to 1), closing the cycle.                             *)
(***************************************************************************)
PostCondition ==
    LET S == CounterExample.state
        A == CounterExample.action
    IN  /\ Cardinality(S) = 12
        /\ {s[2].hr : s \in S} = 1 .. 12
        /\ Cardinality(A) = 12
        /\ \A a \in A :
              a[3][2].hr = IF a[1][2].hr = 12 THEN 1 ELSE a[1][2].hr + 1

=============================================================================