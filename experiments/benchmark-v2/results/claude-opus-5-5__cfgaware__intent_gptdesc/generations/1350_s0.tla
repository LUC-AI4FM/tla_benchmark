---------------------------- MODULE Counter ----------------------------
EXTENDS Naturals

VARIABLE counter

vars == << counter >>

Max == 5

TypeOK == counter \in 1..Max

Init == counter = 1

Increment ==
    /\ counter < Max
    /\ counter' = counter + 1

Stay ==
    /\ counter = Max
    /\ UNCHANGED counter

Next == Increment \/ Stay

Spec == Init /\ [][Next]_vars /\ WF_vars(Increment)

-----------------------------------------------------------------------------
\* Auxiliary invariants

Bounded == counter >= 1 /\ counter <= Max

Inv == TypeOK /\ Bounded

\* Safety properties

StepSafety ==
    [][ \/ (counter < Max /\ counter' = counter + 1)
        \/ (counter = Max /\ counter' = counter)
      ]_vars

Monotonic == [][counter' >= counter]_vars

NoJump == [][counter' <= counter + 1]_vars

StableAtMax == [][counter = Max => counter' = Max]_vars

Safety == StepSafety /\ Monotonic /\ NoJump /\ StableAtMax

\* Liveness property: eventual stabilization at 5

Liveness == <>[](counter = Max)

EventuallyMax == <>(counter = Max)

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => Safety
THEOREM Spec => Liveness
=============================================================================