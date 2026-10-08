---------------------------- MODULE NBAC ----------------------------
EXTENDS Integers, TLC

CONSTANT N
VARIABLES votes, decisions, suspected, crashed

TypeOK == /\ votes \in [1..N -> {"YES", "NO"}]
           /\ decisions \in [1..N -> {"COMMIT", "ABORT", "UND"}]
           /\ suspected \in [1..N -> BOOLEAN]
           /\ crashed \in [1..N -> BOOLEAN]

Init == /\ votes = [i \in 1..N |-> "YES"]  \* arbitrary initialization
        /\ decisions = [i \in 1..N |-> "UND"]
        /\ suspected = [i \in 1..N |-> FALSE]
        /\ crashed = [i \in 1..N |-> FALSE]

SendVote(i) == /\ votes' = [votes EXCEPT ![i] = "SENT"]
               /\ decisions' = decisions
               /\ suspected' = suspected
               /\ crashed' = crashed

ReceiveVotes(i) == /\ votes' = votes
                   /\ decisions' = IF /\ \A j \in 1..N : votes[j] = "YES"
                                        /\ \A j \in 1..N : ~suspected[j]
                                    THEN [decisions EXCEPT ![i] = "COMMIT"]
                                    ELSE [decisions EXCEPT ![i] = "ABORT"]
                   /\ suspected' = suspected
                   /\ crashed' = crashed

Suspect(i) == /\ votes' = votes
               /\ decisions' = decisions
               /\ suspected' = [suspected EXCEPT ![i] = TRUE]
               /\ crashed' = crashed

Crash(i) == /\ votes' = votes
             /\ decisions' = decisions
             /\ suspected' = suspected
             /\ crashed' = [crashed EXCEPT ![i] = TRUE]

Next == \E i \in 1..N : (SendVote(i) \/ ReceiveVotes(i) \/ Suspect(i) \/ Crash(i))

Spec == Init /\ [][Next]_<<votes, decisions, suspected, crashed>>

AgrrLtl == \A i, j \in 1..N : <<decisions[i] = "COMMIT">> ~> <<decisions[j] = "COMMIT">>
                   /\ <<decisions[i] = "ABORT">> ~> <<decisions[j] = "ABORT">>

AbortValidityLtl == \E i \in 1..N : <<votes[i] = "NO">> ~> <<~\E j \in 1..N : decisions[j] = "COMMIT">>

CommitValidityLtl == \A i \in 1..N : <<votes[i] = "YES">> /\ ~<<suspected[i]>> /\ [][~Crash(i)]_crashed
                                  ~> <<decisions[i] = "COMMIT">>

TerminationLtl == \A i \in 1..N : [][~Crash(i)]_crashed /\ [][~Suspect(i)]_suspected
                                ~> <<decisions[i] = "COMMIT">> \/ <<decisions[i] = "ABORT">>
====================================================================