------------------------------- MODULE AugmentedMutex -------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS P  \* Set of processes, e.g., {0, 1}

VARIABLES pc, turn, history, stutterStep

Init == /\ pc = [p \in P |-> "entry"]
        /\ turn = CHOOSE p \in P : TRUE
        /\ history = <<>>
        /\ stutterStep = [p \in P |-> 0]

Next ==
    \/ /\ E \in SUBSET P
       /\ \A p \in P : pc[p] = IF p \in E THEN "entry" ELSE "exit"
       /\ \E p \in E :
            /\ pc' = [pc EXCEPT ![p] = CASE stutterStep[p] = 0 -> "entry1"
                                    [] stutterStep[p] = 1 -> "entry2"
                                    [] stutterStep[p] = 2 -> "critical"]
            /\ turn' = IF stutterStep[p] = 2 THEN p ELSE turn
            /\ history' = <<history, [p \in P |-> turn]>>
            /\ stutterStep' = [stutterStep EXCEPT ![p] = (stutterStep[p] + 1) % 3]
       /\ \A q \notin E : pc'[q] = pc[q]
          /\ stutterStep'[q] = stutterStep[q]
    \/ /\ E \in SUBSET P
       /\ \A p \in P : pc[p] = IF p \in E THEN "critical" ELSE "exit"
       /\ \E p \in E :
            /\ pc' = [pc EXCEPT ![p] = "exit"]
            /\ turn' = turn
            /\ history' = history
            /\ stutterStep' = stutterStep
       /\ \A q \notin E : pc'[q] = pc[q]
          /\ stutterStep'[q] = stutterStep[q]
    \/ /\ E \in SUBSET P
       /\ \A p \in P : pc[p] = IF p \in E THEN "exit" ELSE "entry"
       /\ \E p \in E :
            /\ pc' = [pc EXCEPT ![p] = "entry"]
            /\ turn' = turn
            /\ history' = history
            /\ stutterStep' = [stutterStep EXCEPT ![p] = 0]
       /\ \A q \notin E : pc'[q] = pc[q]
          /\ stutterStep'[q] = stutterStep[q]

Spec == Init /\ [][Next]_<<pc, turn, history, stutterStep>>

TypeOK ==
    /\ pc \in [P -> {"entry", "critical", "exit"}]
    /\ turn \in P
    /\ history \in Seq([P -> P])
    /\ stutterStep \in [P -> {0, 1, 2}]

TurnInvariant ==
    \/ \E p \in P : pc[p] = "critical" /\ turn = p
    \/ \A p \in P : pc[p] \notin {"entry", "critical"}

SpecWithInvariants == Spec /\ WF_<<pc, turn, history, stutterStep>>[Next] /\ TypeOK /\ TurnInvariant

=============================================================================