------------------------------- MODULE ByzantineConsensus -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, F, T
ASSUME F <= T /\ N > 3 * T

VARIABLES values, proposals, decisions, correctProcesses, faultyProcesses, messageCounts

Init == 
    /\ correctProcesses = {p \in 1..N : p \notin faultyProcesses}
    /\ faultyProcesses \subseteq (1..N) /\ Cardinality(faultyProcesses) <= F
    /\ values \in [correctProcesses -> {0, 1}]
    /\ proposals = [p \in 1..N -> {}]
    /\ decisions = [p \in 1..N -> FALSE]
    /\ messageCounts = [p \in correctProcesses -> <<0, 0>>, q \in faultyProcesses -> <<0, 0>>]

Next ==
    \/ \E p \in correctProcesses : 
        ~decisions[p] /\ proposals[p] = {} /\
        (proposals' = [proposals EXCEPT ![p] = {values[p]}]
         /\ UNCHANGED <<correctProcesses, faultyProcesses, values, decisions, messageCounts>>)
    \/ \E p \in correctProcesses :
        ~decisions[p] /\ proposals[p] /= {} /\
        (messageCounts' = [messageCounts EXCEPT ![p] = 
            <<Len({m \in proposals[p] : m = 0}), Len({m \in proposals[p] : m = 1})>>]
         /\ decisions' = [decisions EXCEPT ![p] = 
            CASE messageCounts[p][1] >= N - T -> TRUE
                 [] messageCounts[p][2] >= N - T -> TRUE
                 [] OTHER -> FALSE]
         /\ UNCHANGED <<correctProcesses, faultyProcesses, values, proposals>>)
    \/ \E p \in faultyProcesses :
        ~decisions[p] /\
        (proposals' = [proposals EXCEPT ![p] = {0, 1}]
         /\ messageCounts' = [messageCounts EXCEPT ![p] = <<0, 0>>]
         /\ UNCHANGED <<correctProcesses, faultyProcesses, values, decisions>>)

Spec ==
    Init /\ [][Next]_<<proposals, decisions, messageCounts>>

TypeOK ==
    /\ correctProcesses \subseteq (1..N)
    /\ faultyProcesses \subseteq (1..N) /\ Cardinality(faultyProcesses) <= F
    /\ values \in [correctProcesses -> {0, 1}]
    /\ proposals \in [1..N -> SUBSET {0, 1}]
    /\ decisions \in [1..N -> BOOLEAN]
    /\ messageCounts \in [1..N -> <<Nat, Nat>>]

Safety ==
    /\ TypeOK
    /\ \A p \in correctProcesses : 
        (values[p] = 0 => ~(\E q \in correctProcesses : decisions[q] = TRUE))
    /\ \A p \in correctProcesses :
        (values[p] = 1 => (\A q \in correctProcesses : decisions[q] = TRUE))

Liveness ==
    WF_<<proposals, decisions>>[Next]
    /\ SF_<<proposals, decisions>>[p \in correctProcesses : ~decisions[p]]

THEOREM Spec => []Safety
THEOREM Spec => <>Liveness
=============================================================================