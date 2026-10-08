------------------------------- MODULE NBACProtocol -------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N \* Number of processes
ASSUME N \in Nat /\ N > 0

VARIABLES votes, receivedVotes, failureDetector, decisions

Init == 
    /\ votes \in [1..N -> {YES, NO}]
    /\ receivedVotes = [p \in 1..N |-> {}]
    /\ failureDetector \in [1..N -> {"all-correct", "crash"}]
    /\ decisions = [p \in 1..N |-> UNDECIDED]

Next ==
    \/ \E p \in 1..N : 
        \/ /\ failureDetector[p] = "all-correct"
           /\ receivedVotes[p] = {v \in [1..N -> {YES, NO}] : \A q \in 1..N : v[q] = votes[q]}
           /\ decisions[p] = UNDECIDED
           /\ (decisions' = [decisions EXCEPT ![p] = IF \A q \in 1..N : votes[q] = YES THEN COMMIT ELSE ABORT])
        \/ /\ failureDetector[p] = "crash"
           /\ decisions[p] = UNDECIDED
           /\ (decisions' = [decisions EXCEPT ![p] = ABORT])
    \/ \E p, q \in 1..N : 
        \/ /\ q /= p
           /\ receivedVotes[p][q] \notin {YES, NO}
           /\ (receivedVotes' = [receivedVotes EXCEPT ![p][q] = votes[q]])

Spec ==
    Init /\ [][Next]_<<votes, receivedVotes, failureDetector, decisions>>

TypeSafety ==
    /\ votes \in [1..N -> {YES, NO}]
    /\ receivedVotes \in [1..N -> {[1..N -> {YES, NO}] -> {YES, NO}}]
    /\ failureDetector \in [1..N -> {"all-correct", "crash"}]
    /\ decisions \in [1..N -> {UNDECIDED, COMMIT, ABORT}]

Validity ==
    \/ \E p \in 1..N : decisions[p] = COMMIT
       /\ \A q \in 1..N : votes[q] = YES
    \/ \A p \in 1..N : decisions[p] /= COMMIT

Invariants == TypeSafety /\ Validity

WF ==
    WF_WeakFair({p \in 1..N : failureDetector[p] = "all-correct" /\ decisions[p] = UNDECIDED}, Next)

CompleteSpec == Spec /\ Invariants /\ WF
=============================================================================