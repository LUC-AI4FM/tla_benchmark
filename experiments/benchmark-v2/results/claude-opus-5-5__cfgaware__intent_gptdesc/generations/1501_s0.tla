---------------------------- MODULE FactorialCounter ----------------------------
EXTENDS Naturals

(***************************************************************************)
(* A single integer-valued counter. Each step atomically assigns the       *)
(* counter either the factorial of a small constant (short update) or the  *)
(* factorial of a larger constant (long update).                           *)
(***************************************************************************)

SmallN == 3
LargeN == 9

\* Total and terminating on Nat: the argument strictly decreases to 0.
RECURSIVE Factorial(_)
Factorial(n) == IF n = 0 THEN 1 ELSE n * Factorial(n - 1)

ShortResult == Factorial(SmallN)   \* 6
LongResult  == Factorial(LargeN)   \* 362880

FactorialValues == {ShortResult, LongResult}

VARIABLE counter

vars == <<counter>>

Init == counter = 0

ShortUpdate == counter' = ShortResult

LongUpdate == counter' = LongResult

Next == ShortUpdate \/ LongUpdate

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

---------------------------------------------------------------------------
(* Safety properties *)

TypeOK == counter \in Nat

\* After initialization the counter only ever holds a factorial result.
CounterInv == counter \in {0} \cup FactorialValues

\* Every non-initial value equals one of the concrete factorial values.
CounterIsFactorial == counter # 0 => counter \in FactorialValues

\* Every transition assigns exactly one of the factorial values.
StepAssignsFactorial == [][counter' \in FactorialValues]_vars

\* The two values are distinct, so a step assigns exactly one of them.
DistinctResults == ShortResult # LongResult

---------------------------------------------------------------------------
(* Liveness and deadlock-freedom *)

\* Some transition is always enabled.
NoDeadlock == []ENABLED Next

ShortAlwaysEnabled == [](ENABLED ShortUpdate)
LongAlwaysEnabled  == [](ENABLED LongUpdate)

\* The counter eventually takes a factorial value and keeps one from then on.
EventuallyFactorial == <>[](counter \in FactorialValues)

THEOREM Spec => []CounterInv
THEOREM Spec => StepAssignsFactorial
THEOREM Spec => NoDeadlock
THEOREM Spec => EventuallyFactorial
================================================================================