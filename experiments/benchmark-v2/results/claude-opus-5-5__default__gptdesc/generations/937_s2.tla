--------------------------- MODULE LiveHourClock ---------------------------
(***************************************************************************)
(* Adds a liveness requirement to the hour clock of module HourClock.      *)
(* HourClock defines:                                                      *)
(*   VARIABLE hr                                                           *)
(*   HCini == hr \in (1 .. 12)                                             *)
(*   HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1                          *)
(*   HC    == HCini /\ [][HCnxt]_hr                                        *)
(***************************************************************************)
EXTENDS HourClock, TLC, FiniteSets

(***************************************************************************)
(* The live specification: the clock must keep ticking.                    *)
(***************************************************************************)
LSpec == HC /\ WF_hr(HCnxt)

(***************************************************************************)
(* Liveness and safety properties implied by LSpec.                        *)
(***************************************************************************)
AlwaysTick  == []<><<HCnxt>>_hr

AllTimes    == \A n \in 1..12 : []<>(hr = n)

TypeCorrect == []HCini

THEOREM LSpec => AlwaysTick /\ AllTimes /\ TypeCorrect

(***************************************************************************)
(* A settling property that LSpec does NOT satisfy. The clock never        *)
(* settles on a single value. When TLC checks Settle, it reports a         *)
(* counterexample.                                                         *)
(***************************************************************************)
Settle == <>[](hr = 12)

(***************************************************************************)
(* Postcondition describing the counterexample's structure. It is a lasso  *)
(* of 12 distinct states covering every hour. Its 12 transitions loop      *)
(* back to the start.                                                      *)
(***************************************************************************)
PostCondition ==
    /\ Cardinality(CounterExample.state) = 12
    /\ Cardinality(CounterExample.action) = 12
    /\ { s[2].hr : s \in CounterExample.state } = 1..12
    /\ \A a \in CounterExample.action :
          a[3][2].hr = IF a[1][2].hr # 12 THEN a[1][2].hr + 1 ELSE 1
=============================================================================