------------------------------- MODULE GCDLoop -------------------------------
EXTENDS Integers, TLC

CONSTANTS 
    \* Constants if any

VARIABLES u, v, pc

Init == 
    /\ u = 24 
    /\ v \in 1..50
    /\ pc = "start"

StepStart ==
    /\ pc = "start"
    /\ pc' = "loop"

StepLoop ==
    /\ pc = "loop"
    /\ \/ /\ u < v 
           /\ u' = v
           /\ v' = u
           /\ pc' = "loop"
          \/ /\ u >= v 
           /\ u' = u - v
           /\ v' = v
           /\ pc' = "loop"

StepDone ==
    /\ pc = "done"
    /\ pc' = "done"

Next == 
    \/ StepStart
    \/ StepLoop
    \/ StepDone

Spec == 
    /\ Init
    /\ [][Next]_<<u, v, pc>>
    /\ WF_next(<<u, v, pc>>, Next)

Done == u = 0 /\ pc = "loop"

InvariantGCD ==
    \A a \in 1..50 : Done => v = Gcd(24, a)

SpecWithInvariants ==
    Spec /\ [](InvariantGCD)

THEOREM SpecWithInvariants

=============================================================================