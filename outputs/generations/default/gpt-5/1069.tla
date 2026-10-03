------------------------------ MODULE TerminationDetectionRing ------------------------------

EXTENDS Naturals

CONSTANTS 
    N,          \* number of nodes in the ring; assumed positive
    MaxSteps    \* bound for bounded model checking

ASSUME N \in Nat \ {0}
ASSUME MaxSteps \in Nat

Node == 1..N

NextNode(i) == IF i = N THEN 1 ELSE i + 1

VARIABLES 
    active,     \* [Node -> BOOLEAN], whether node i is active
    pending,    \* [Node -> Nat], number of pending messages destined to node i
    detected,   \* BOOLEAN, whether global termination has been detected
    step        \* Nat, logical step counter for bounded model checking

vars == << active, pending, detected, step >>

AllInactive == \A i \in Node: ~active[i]
NoPending  == \A i \in Node: pending[i] = 0
AllTerminated == AllInactive /\ NoPending

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending \in [Node -> Nat]
    /\ detected = FALSE
    /\ step = 0

Send(i) ==
    /\ i \in Node
    /\ active[i]
    /\ LET j == NextNode(i) IN
       pending' = [pending EXCEPT ![j] = @ + 1]
    /\ active' = active
    /\ detected' = detected
    /\ step' = step + 1

Receive(j) ==
    /\ j \in Node
    /\ pending[j] > 0
    /\ pending' = [pending EXCEPT ![j] = @ - 1]
    /\ active' = [active EXCEPT ![j] = TRUE]
    /\ detected' = detected
    /\ step' = step + 1

Terminate(i) ==
    /\ i \in Node
    /\ active[i]
    /\ pending[i] = 0
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ pending' = pending
    /\ detected' = detected
    /\ step' = step + 1

DetectTermination ==
    /\ ~detected
    /\ AllTerminated
    /\ detected' = TRUE
    /\ active' = active
    /\ pending' = pending
    /\ step' = step + 1

Next ==
    \/ \E i \in Node: Send(i)
    \/ \E j \in Node: Receive(j)
    \/ \E i \in Node: Terminate(i)
    \/ DetectTermination

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(DetectTermination)

\* Safety invariants (state predicates)
TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending \in [Node -> Nat]
    /\ detected \in BOOLEAN
    /\ step \in Nat

DetectionImpliesActualTermination ==
    detected => AllTerminated

\* Liveness and stability properties (temporal formulas)
TerminationStable ==
    [](AllTerminated => []AllTerminated)

DetectionStable ==
    [](detected => []detected)

TerminationLeadsToDetection ==
    AllTerminated ~> detected

\* State constraint for bounded model checking (to be used as TLC STATE CONSTRAINT)
StateConstraint ==
    step < MaxSteps

=============================================================================