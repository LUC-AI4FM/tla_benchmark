------------------------------- MODULE AsyncCommitProtocol -------------------------------

CONSTANTS N \* Number of processes
          InitialVotes \* Function from process ID to initial vote (YES or NO)

VARIABLES votes, \* Votes received by each process
            suspected, \* Set of suspected processes
            decisions, \* Decision made by each process (COMMIT or ABORT)
            sentVotes \* Sent votes by each process

\* Process IDs are integers from 1 to N
ProcIDs == 1..N

\* Possible vote values
VoteValues == {"YES", "NO"}

\* Possible decision values
DecisionValues == {"COMMIT", "ABORT"}

\* Initial state
Init == /\ votes = [p \in ProcIDs |-> {}]
        /\ suspected = {}
        /\ decisions = [p \in ProcIDs |-> UNDECIDED]
        /\ sentVotes = [p \in ProcIDs |-> FALSE]

\* Sending a vote message
SendVote ==
    CHOOSE p \in (ProcIDs \ {p' \in ProcIDs : sentVotes[p']}) :
        /\ sentVotes' = [sentVotes EXCEPT ![p] = TRUE]
        /\ UNCHANGED <<votes, suspected, decisions>>

\* Delivering a vote message to recipient
DeliverVote ==
    CHOOSE p \in (ProcIDs \ {p' \in ProcIDs : sentVotes[p']}) :
    CHOOSE q \in (ProcIDs \ {p}) :
        /\ votes' = [votes EXCEPT ![q] = votes[q] \cup {InitialVotes[p]}]
        /\ UNCHANGED <<sentVotes, suspected, decisions>>

\* Process crashes and is permanently suspected
Crash ==
    CHOOSE p \in ProcIDs :
        /\ suspected' = suspected \cup {p}
        /\ UNCHANGED <<votes, sentVotes, decisions>>

\* Local decision based on received votes and suspicions
Decide ==
    CHOOSE p \in (ProcIDs \ {p' \in ProcIDs : decisions[p'] # "UNDECIDED"}) :
        LET localVotes == votes[p]
            allSuspected == suspected = ProcIDs
        IN /\ IF (\E v \in localVotes : v = "NO") \/ allSuspected THEN
                decisions' = [decisions EXCEPT ![p] = "ABORT"]
           ELSE IF (\A v \in localVotes : v = "YES") /\ (suspected = {}) THEN
                decisions' = [decisions EXCEPT ![p] = "COMMIT"]
           ELSE
                decisions' = decisions
        /\ UNCHANGED <<votes, suspected, sentVotes>>

\* Type invariants
TypeOK ==
    /\ votes \in [ProcIDs -> SUBSET VoteValues]
    /\ suspected \in SUBSET ProcIDs
    /\ decisions \in [ProcIDs -> {"UNDECIDED"} \cup DecisionValues]
    /\ sentVotes \in [ProcIDs -> BOOLEAN]

\* Agreement: no two nonfaulty processes decide different outcomes
AgrrLtl ==
    LET correctProcesses == ProcIDs \ suspected
        committed == {p \in correctProcesses : decisions[p] = "COMMIT"}
        aborted == {p \in correctProcesses : decisions[p] = "ABORT"}
    IN \/ committed = {}
       \/ aborted = {}

\* Abort validity: if any process initially votes NO, then no process may decide COMMIT
AbortValidityLtl ==
    LET initialNO == (\E p \in ProcIDs : InitialVotes[p] = "NO")
        committed == (\E p \in ProcIDs : decisions[p] = "COMMIT")
    IN \/ ~initialNO
       \/ ~committed

\* Commit validity: if all processes initially vote YES and no process is suspected at that time, then no process decides ABORT (and no crashes occur thereafter)
CommitValidityLtl ==
    LET initialYES == (\A p \in ProcIDs : InitialVotes[p] = "YES")
        aborted == (\E p \in ProcIDs : decisions[p] = "ABORT")
        crashed == (\E p \in ProcIDs : p \in suspected)
    IN \/ ~initialYES
       \/ ~aborted
       \/ ~crashed

\* Termination under stability: if no further crashes occur and failure detector stops suspecting any noncrashed process, then every noncrashed process eventually decides (COMMIT or ABORT)
TerminationLtl ==
    LET stable == (\A p \in ProcIDs : decisions[p] # "UNDECIDED")
        noCrashes == suspected = {}
    IN \/ ~noCrashes
       \/ stable

\* Next state relation
Next ==
    \/ SendVote
    \/ DeliverVote
    \/ Crash
    \/ Decide

\* Specification
Spec ==
    Init /\ [][Next]_<<votes, suspected, decisions, sentVotes>>
          /\ WF_[SendVote]_<<votes, suspected, decisions, sentVotes>>
          /\ WF_[DeliverVote]_<<votes, suspected, decisions, sentVotes>>
          /\ SF_[Crash]_<<votes, suspected, decisions, sentVotes>>
          /\ SF_[Decide]_<<votes, suspected, decisions, sentVotes>>

=============================================================================