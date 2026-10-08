------------------------------- MODULE AtomicCommitment -------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N \* Number of processes
ASSUME N \in Nat /\ N > 0

VARIABLES 
    votes,          \* Votes of each process: [1..N -> {"YES", "NO"}}
    deliveredVotes, \* Delivered votes for each process: [1..N -> [1..N -> {"YES", "NO"}]]
    crashed,        \* Set of crashed processes
    suspected,      \* Suspected crashed processes: [1..N -> BOOLEAN]
    decided,        \* Decision made by each process: [1..N -> {"commit", "abort", FALSE}]
    strongFairness  \* Boolean indicating if the failure detector is strongly fair

Init == 
    /\ votes = [p \in 1..N |-> CHOOSE v \in {"YES", "NO"}]
    /\ deliveredVotes = [p \in 1..N |-> [q \in 1..N |-> FALSE]]
    /\ crashed = {}
    /\ suspected = [p \in 1..N |-> FALSE]
    /\ decided = [p \in 1..N |-> FALSE]

VoteMessage ==
    CHOOSE p, q \in 1..N : \/ votes[p] \notin {"YES", "NO"}
                           \/ deliveredVotes[q][p] = votes[p]
                           \/ q \in crashed
                           \/ suspected[q]
    /\ deliveredVotes' = [deliveredVotes EXCEPT ![q][p] = votes[p]]

Crash ==
    CHOOSE p \in 1..N : p \notin crashed
    /\ crashed' = crashed \cup {p}
    /\ decided' = [decided EXCEPT ![p] = FALSE]

Suspect ==
    CHOOSE p, q \in 1..N : suspected[q][p] = suspected[q][p]
    /\ suspected' = [suspected EXCEPT ![q][p] = ~suspected[q][p]]

DecideCommit ==
    CHOOSE p \in 1..N : \/ decided[p] \in {"commit", "abort"}
                         \/ (\E q \in 1..N \ {p} : deliveredVotes[p][q] = "NO")
                         \/ (\A q \in 1..N \ crashed : deliveredVotes[p][q] = "YES")
    /\ decided' = [decided EXCEPT ![p] = IF (\A q \in 1..N \ crashed : deliveredVotes[p][q] = "YES") THEN "commit" ELSE "abort"]

DecideAbort ==
    CHOOSE p \in 1..N : \/ decided[p] \in {"commit", "abort"}
                        \/ (\E q \in 1..N \ {p} : deliveredVotes[p][q] = "NO")
    /\ decided' = [decided EXCEPT ![p] = IF (\E q \in 1..N \ {p} : deliveredVotes[p][q] = "NO") THEN "abort" ELSE decided[p]]

Next ==
    \/ VoteMessage
    \/ Crash
    \/ Suspect
    \/ DecideCommit
    \/ DecideAbort

Spec == 
    /\ Init
    /\ [][Next]_<<votes, deliveredVotes, crashed, suspected, decided>>
    /\ WF_StrongFairness(<<votes, deliveredVotes, crashed, suspected, decided>>, strongFairness)

Agreement ==
    \A p, q \in 1..N : \/ p \in crashed \/ q \in crashed \/ decided[p] = FALSE \/ decided[q] = FALSE \/ decided[p] = decided[q]

ValidityCommit ==
    \A p \in 1..N : \/ p \in crashed \/ decided[p] # "commit" \/ (\A q \in 1..N \ crashed : votes[q] = "YES")

ValidityAbort ==
    \A p \in 1..N : \/ p \in crashed \/ decided[p] # "abort" \/ (\E q \in 1..N \ {p} : votes[q] = "NO")

Safety == Agreement /\ ValidityCommit /\ ValidityAbort

Liveness ==
    \A p \in 1..N \ crashed :
        <>(decided[p] \in {"commit", "abort"})_<<votes, deliveredVotes, crashed, suspected, decided>>

WF_StrongFairness(vars, strongFairness) ==
    \/ ~strongFairness
    \/ WF_vars(<>)

=============================================================================