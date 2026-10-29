------------------------------ MODULE HourClock2 ------------------------------
(***************************************************************************)
(* The hour clock from HourClock, with a liveness requirement added.       *)
(* The HourClock definitions are restated here so that the module parses   *)
(* on its own.                                                             *)
(***************************************************************************)
EXTENDS Naturals, Sequences

VARIABLES hr

vars == <<hr>>

-----------------------------------------------------------------------------
(* Definitions from HourClock *)

HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

-----------------------------------------------------------------------------
(* Standard names *)

Init == HCini

Next == HCnxt

(* Clock specification with weak fairness on the tick step *)
LSpec == HC /\ WF_hr(HCnxt)

Spec == LSpec

-----------------------------------------------------------------------------
(* Safety *)

TypeOK == HCini

AlwaysTyped == []HCini

-----------------------------------------------------------------------------
(* Liveness *)

(* The clock ticks infinitely often *)
TicksInfinitelyOften == []<><<HCnxt>>_hr

(* Every hour value from 1 through 12 recurs infinitely often *)
AllHoursRecur == \A h \in 1 .. 12 : []<>(hr = h)

LiveProperties == TicksInfinitelyOften /\ AllHoursRecur /\ AlwaysTyped

THEOREM LSpec => TicksInfinitelyOften /\ AllHoursRecur /\ []HCini

-----------------------------------------------------------------------------
(* Settling property, which LSpec does NOT satisfy: the clock eventually   *)
(* settles at one hour value forever.                                      *)

Settles == \E h \in 1 .. 12 : <>[](hr = h)

(***************************************************************************)
(* Postcondition describing the structure of a counterexample to Settles. *)
(* The counterexample is a lasso-shaped behavior: a finite sequence of     *)
(* states in which each state's hr is followed by its HCnxt successor, and *)
(* the last state loops back to the first. Because the loop goes through  *)
(* all twelve hour values, hr never settles at a single value.             *)
(***************************************************************************)
IsLassoCounterexample(trace) ==
    /\ Len(trace) = 12
    /\ \A i \in 1 .. Len(trace) : trace[i].hr \in 1 .. 12
    /\ \A i \in 1 .. (Len(trace) - 1) :
          trace[i + 1].hr = IF trace[i].hr # 12 THEN trace[i].hr + 1 ELSE 1
    /\ trace[1].hr = IF trace[Len(trace)].hr # 12
                        THEN trace[Len(trace)].hr + 1
                        ELSE 1
    /\ \A h \in 1 .. 12 : \E i \in 1 .. Len(trace) : trace[i].hr = h

CounterexampleTrace == [i \in 1 .. 12 |-> [hr |-> i]]

PostCondition == IsLassoCounterexample(CounterexampleTrace)

=============================================================================