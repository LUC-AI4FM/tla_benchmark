---------------------------- MODULE FactorialCounter ----------------------------
EXTENDS Naturals

CONSTANTS Small, Large

ASSUME SmallLargeAssumption ==
    /\ Small \in Nat
    /\ Large \in Nat
    /\ Small = 3
    /\ Large = 9

VARIABLE counter

vars == <<counter>>

\* Total, terminating factorial on naturals (recursion decreases toward 0).
RECURSIVE Fact(_)
Fact(n) == IF n <= 1 THEN 1 ELSE n * Fact(n - 1)

ShortResult == Fact(Small)   \* 3! = 6
LongResult  == Fact(Large)   \* 9! = 362880

FactorialValues == {ShortResult, LongResult}

-----------------------------------------------------------------------------
Init == counter = 0

\* Short update: atomically assigns factorial of the small constant
ShortUpdate == counter' = ShortResult

\* Long update: atomically assigns factorial of the large constant
LongUpdate == counter' = LongResult

Next == ShortUpdate \/ LongUpdate

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(ShortUpdate)
        /\ WF_vars(LongUpdate)

-----------------------------------------------------------------------------
\* Safety properties

TypeOK == counter \in Nat

\* The counter always holds the initial value or one of the factorial results
CounterInvariant == counter \in {0} \cup FactorialValues

\* Once any update has occurred, the counter equals a factorial value
AfterUpdateInvariant == counter # 0 => counter \in FactorialValues

\* Every transition assigns exactly one of the factorial values
TransitionAssignsFactorial ==
    [][ /\ counter' \in FactorialValues
        /\ (counter' = ShortResult) # (counter' = LongResult) ]_vars

\* The computed results are the correct concrete values
FactorialCorrect == ShortResult = 6 /\ LongResult = 362880

-----------------------------------------------------------------------------
\* Liveness properties

\* No deadlock: some transition is always enabled
NoDeadlock == [](ENABLED Next)

\* Both kinds of update are always available
BothAlwaysEnabled == [](ENABLED ShortUpdate /\ ENABLED LongUpdate)

\* Executions may take either kind of update indefinitely
ShortInfinitelyOften == []<>(counter = ShortResult)
LongInfinitelyOften  == []<>(counter = LongResult)

EventuallyFactorial == <>(counter \in FactorialValues)

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []CounterInvariant
THEOREM Spec => []AfterUpdateInvariant
THEOREM Spec => TransitionAssignsFactorial
THEOREM Spec => NoDeadlock
THEOREM Spec => ShortInfinitelyOften /\ LongInfinitelyOften
=============================================================================