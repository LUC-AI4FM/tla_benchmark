---- MODULE LockHS ----

CONSTANTS N \* Number of processes

VARIABLES pc, turn, h_turn, s

\* Importing necessary modules
EXTENDS Integers, FiniteSets, Stuttering, Peterson

\* Initial condition for the extended lock
InitHS == Init /\ h_turn = 1 /\ s = top

\* Type invariants for all variables
TypeOKHS ==
    /\ pc \in [1..N -> {"l0", "l1", "cs", "l2"}]
    /\ turn \in 1..N
    /\ h_turn \in 1..N
    /\ s \in Stuttering

\* Consistency invariants linking stuttering state and program counters to h_turn
InvHS ==
    /\ (/\ pc[turn] = "l0" => s = top)
    /\ (/\ pc[turn] = "l1" => s \in {top, "s1", "s2"})
    /\ (/\ pc[turn] = "cs" => s = top)
    /\ (/\ pc[turn] = "l2" => s = top)

\* Mutual exclusion invariant inherited from Lock
LockInv ==
    \/ turn = 0
    \/ \A i \in 1..N : i # turn => pc[i] \notin {"cs"}

\* Action l1 wrapped with stuttering steps and updating h_turn appropriately
l1HS ==
    [pc EXCEPT ![turn] = "l1"] /\ s' = "s1" /\ UNCHANGED <<h_turn, turn>>
    \/ [pc EXCEPT ![turn] = "l1"] /\ s = "s1" /\ s' = "s2" /\ h_turn' = turn /\ UNCHANGED turn
    \/ [pc EXCEPT ![turn] = "cs"] /\ s = "s2" /\ s' = top /\ UNCHANGED <<h_turn, turn>>

\* Other actions proceed without stuttering and leave h_turn unchanged
l0 == [pc EXCEPT ![turn] = "l1"] /\ UNCHANGED <<h_turn, s>>
cs == [pc EXCEPT ![turn] = "l2"] /\ UNCHANGED <<h_turn, s>>
l2 == [pc EXCEPT ![turn] = "l0"] /\ turn' = 0 /\ UNCHANGED h_turn

\* Overall specification as a safety property over the combined variable tuple
SpecHS ==
    InitHS /\ [][[l0 \/ l1HS \/ cs \/ l2]_<<pc, turn, h_turn, s>>]_<<pc, turn, h_turn, s>>

\* Translation functions for Peterson's algorithm
pc_translation == [i \in 1..N |-> IF pc[i] = "l0" THEN 0 ELSE IF pc[i] = "l1" THEN 1 ELSE IF pc[i] = "cs" THEN 2 ELSE 3]
c_translation == turn

\* Peterson's specification instantiated with translations
PSpec ==
    /\ InitP(c_translation)
    /\ [][[l0P \/ l1P \/ csP \/ l2P]_<<pcP, c>>]_<<pcP, c>>
    /\ \A i \in 1..N : pcP[i] = pc_translation[i]

\* Assertions for bidirectional refinement
Spec ==
    SpecHS /\ TypeOKHS /\ InvHS /\ LockInv

THEOREM Spec => PSpec

====