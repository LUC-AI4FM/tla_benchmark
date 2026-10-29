------------------------------ MODULE HourClock2 ------------------------------
(***************************************************************************)
(* The hour clock of module HourClock, augmented with a liveness          *)
(* requirement.  The HourClock definitions are included inline so that    *)
(* this module parses on its own.                                         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLCExt

VARIABLE hr

-----------------------------------------------------------------------------
(***************************************************************************)
(* The hour clock specification HC, as in module HourClock.               *)
(***************************************************************************)
HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

Init == HCini
Next == HCnxt

-----------------------------------------------------------------------------
(***************************************************************************)
(* The live specification: HC together with weak fairness of HCnxt.       *)
(***************************************************************************)
LSpec == HC /\ WF_hr(HCnxt)

Spec == LSpec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Temporal properties.                                                   *)
(***************************************************************************)

\* The clock ticks infinitely often.
AlwaysTick == []<><<HCnxt>>_hr

\* Every hour value from 1 through 12 recurs infinitely often.
AllTimes == \A n \in 1 .. 12 : []<>(hr = n)

\* The initial-state typing condition remains always true.
TypeCorrect == []HCini

\* Safety invariant used for model checking.
TypeInvariant == HCini

THEOREM LSpec => AlwaysTick /\ AllTimes /\ TypeCorrect

-----------------------------------------------------------------------------
(***************************************************************************)
(* A "settling" property that LSpec violates.  The clock never settles at *)
(* a single value, because it keeps ticking through all 12 hours.         *)
(***************************************************************************)
Settle == <>[](hr = 12)

(***************************************************************************)
(* The postcondition describes the concrete counterexample structure TLC  *)
(* should produce when checking Settle.  The counterexample is a lasso of *)
(* 12 distinct states that visits every hour 1 through 12 exactly once.   *)
(* It also contains 12 transitions, one HCnxt step from each state,       *)
(* including the step from 12 back to 1 that closes the loop.            *)
(***************************************************************************)
PostCondition ==
    /\ Cardinality(CounterExample.state) = 12
    /\ { s[2].hr : s \in CounterExample.state } = 1 .. 12
    /\ Cardinality(CounterExample.action) = 12
    /\ \A a \in CounterExample.action :
          LET from == a[1][2].hr
              to   == a[3][2].hr
          IN  to = IF from # 12 THEN from + 1 ELSE 1

=============================================================================