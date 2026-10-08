------------------------------- MODULE AtomicCommitment -------------------------------

CONSTANTS N \* Number of processes

VARIABLES votes, decisions, suspicions, deliveredMessages, crashed

\* TypeOK is a predicate that checks if the types are as expected
TypeOK == /\ votes \in [1..N -> {"YES", "NO"}]
          /\ decisions \in [1..N -> {"COMMIT", "ABORT", "UNDECIDED"}]
          /\ suspicions \in [1..N -> BOOLEAN] \* TRUE means suspected crashed
          /\ deliveredMessages \in [1..N -> SUBSET [1..N -> {"YES", "NO"}}]
          /\ crashed \in SUBSET 1..N

\* Initial predicate: All processes start with a vote, no decisions made, no suspicions, empty message boxes, and no crashes
Init == /\ votes = [p \in 1..N |-> CHOOSE v \in {"YES", "NO"}]
        /\ decisions = [p \in 1..N |-> "UNDECIDED"]
        /\ suspicions = [p \in 1..N |-> FALSE]
        /\ deliveredMessages = [p \in 1..N |-> {}]
        /\ crashed = {}

\* Next state relation
Next == \/ \/ \E p \notin crashed : \/ \* Message sending phase
                        \/ \E q \notin crashed, v \in {"YES", "NO"} :
                           /\ deliveredMessages' = [deliveredMessages EXCEPT ![p] = deliveredMessages[p] \cup {[q |-> v]}]
                           /\ UNCHANGED <<votes, decisions, suspicions, crashed>>
                    \/ \/ \* Message receiving phase
                        \/ \E q \notin crashed, m \in deliveredMessages[p], v \in {"YES", "NO"} :
                           /\ votes' = [votes EXCEPT ![p] = IF votes[p] = "YES" THEN votes[p] ELSE v]
                           /\ UNCHANGED <<decisions, suspicions, deliveredMessages, crashed>>
                    \/ \/ \* Crash event
                        \/ \E p \notin crashed :
                           /\ crashed' = crashed \cup {p}
                           /\ UNCHANGED <<votes, decisions, suspicions, deliveredMessages>>
                    \/ \/ \* Suspicions change (failure detector)
                        \/ \E p \in 1..N, s \in BOOLEAN :
                           /\ suspicions' = [suspicions EXCEPT ![p] = s]
                           /\ UNCHANGED <<votes, decisions, deliveredMessages, crashed>>

\* Specification
Spec == Init /\ [][Next]_<<votes, decisions, suspicions, deliveredMessages, crashed>>

\* Agreement: No two non-crashed processes decide differently
Agreement == \A p1, p2 \notin crashed :
               \/ decisions[p1] = "UNDECIDED"
               \/ decisions[p2] = "UNDECIDED"
               \/ decisions[p1] = decisions[p2]

\* Validity: If all processes vote YES and no new crash suspicions prevent progress, then the system may decide commit
             \* If any process votes NO then no correct process may decide commit
Validity == \/ \E p \in 1..N : votes[p] = "NO" /\ decisions[p] = "COMMIT"
            \/ \A p \in 1..N : votes[p] = "YES" => (\A q \notin crashed : decisions[q] \in {"COMMIT", "UNDECIDED"})

\* Termination: If a sufficiently strong eventual accuracy condition holds for the failure detector, then every non-crashed process must eventually decide
Termination == WF_next(<<votes, decisions, suspicions, deliveredMessages, crashed>>) /\ 
               [](\/ \E p \notin crashed : decisions[p] \in {"COMMIT", "ABORT"})

\* Invariants and Temporal Properties
INVARSPEC TypeOK /\ Agreement /\ Validity

LIVENESS << votes, decisions, suspicions, deliveredMessages, crashed >> == Termination

=============================================================================