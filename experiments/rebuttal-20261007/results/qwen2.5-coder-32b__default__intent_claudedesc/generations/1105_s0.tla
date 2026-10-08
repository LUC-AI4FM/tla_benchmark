------------------------------- MODULE NBAC -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N \* Number of processes
ASSUME N \in Nat /\ N > 0

VARIABLES votes, decisions, suspected, voteSent

Init == 
    /\ votes = [p \in 1..N -> CHOOSE v \in {"YES", "NO"}] \* Arbitrary initial votes
    /\ decisions = [p \in 1..N -> FALSE]
    /\ suspected = {}
    /\ voteSent = {}

Next ==
    \/ \/ \E p \in 1..N : 
            \lnot (p \in voteSent) 
            /\ \lnot (p \in suspected)
            /\ votes[p] \in {"YES", "NO"}
            /\ UNCHANGED <<decisions, suspected>>
            /\ voteSent' = voteSent \cup {p}
       \/ \/ \E p \in 1..N : 
                p \in voteSent
                /\ \lnot (p \in suspected)
                /\ \E q \in 1..N :
                    q \notin suspected
                    /\ votes[q] = "NO"
                    /\ decisions' = [decisions EXCEPT ![p] = TRUE]
                    /\ UNCHANGED <<votes, suspected, voteSent>>
           \/ \/ \E p \in 1..N : 
                   p \in voteSent
                   /\ (p \in suspected \/ \E q \in 1..N : q \in suspected)
                   /\ decisions' = [decisions EXCEPT ![p] = TRUE]
                   /\ UNCHANGED <<votes, suspected, voteSent>>
              \/ \/ \E p \in 1..N :
                      p \in voteSent
                      /\ \lnot (p \in suspected)
                      /\ \A q \in 1..N : q \notin suspected /\ votes[q] = "YES"
                      /\ decisions' = [decisions EXCEPT ![p] = TRUE]
                      /\ UNCHANGED <<votes, suspected, voteSent>>
                 \/ \/ \E p \in 1..N :
                         p \notin voteSent
                         /\ suspected' = suspected \cup {p}
                         /\ UNCHANGED <<votes, decisions, voteSent>>

Spec ==
    /\ Init
    /\ [][Next]_<<decisions, votes, suspected, voteSent>>
    /\ WF_next(<<decisions, votes, suspected, voteSent>>)

\* Correctness properties

Agreement ==
    \A p1, p2 \in 1..N :
        decisions[p1] = TRUE => decisions[p2] = TRUE

AbortValidity ==
    \E p \in 1..N : votes[p] = "NO" => \A q \in 1..N : decisions[q] = FALSE

CommitValidity ==
    (\A p \in 1..N : votes[p] = "YES") /\ (suspected = {}) => \A q \in 1..N : decisions[q] = TRUE

Termination ==
    []<>(\A p \in 1..N : decisions[p] = TRUE \/ decisions[p] = FALSE)

=============================================================================