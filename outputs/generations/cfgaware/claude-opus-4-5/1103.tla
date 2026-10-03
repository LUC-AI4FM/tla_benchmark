-------------------------------- MODULE NBAC --------------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

Votes == {"YES", "NO"}
Decisions == {"COMMIT", "ABORT", "UNDECIDED"}
States == {"WORKING", "VOTED", "DECIDED", "CRASHED"}

VARIABLES
    pcState,      \* Process state: WORKING, VOTED, DECIDED, or CRASHED
    vote,         \* Vote of each process: YES or NO
    decision,     \* Decision of each process: COMMIT, ABORT, or UNDECIDED
    failureDetector, \* Local failure detector: TRUE if crash detected
    msgs,         \* Set of messages in transit
    crashed       \* Set of crashed processes

vars == <<pcState, vote, decision, failureDetector, msgs, crashed>>

\* Message types
VoteMsg(p, v) == [type |-> "VOTE", proc |-> p, vote |-> v]
DecisionMsg(d) == [type |-> "DECISION", decision |-> d]

TypeOK ==
    /\ pcState \in [Procs -> States]
    /\ vote \in [Procs -> Votes]
    /\ decision \in [Procs -> Decisions]
    /\ failureDetector \in [Procs -> BOOLEAN]
    /\ msgs \subseteq ([type: {"VOTE"}, proc: Procs, vote: Votes] \cup 
                       [type: {"DECISION"}, decision: {"COMMIT", "ABORT"}])
    /\ crashed \subseteq Procs

Init ==
    /\ pcState = [p \in Procs |-> "WORKING"]
    /\ vote \in [Procs -> Votes]
    /\ decision = [p \in Procs |-> "UNDECIDED"]
    /\ failureDetector = [p \in Procs |-> FALSE]
    /\ msgs = {}
    /\ crashed = {}

\* Process p casts its vote and broadcasts it
CastVote(p) ==
    /\ pcState[p] = "WORKING"
    /\ pcState' = [pcState EXCEPT ![p] = "VOTED"]
    /\ msgs' = msgs \cup {VoteMsg(p, vote[p])}
    /\ UNCHANGED <<vote, decision, failureDetector, crashed>>

\* Received votes for process p
ReceivedVotes(p) ==
    {m.vote : m \in {m \in msgs : m.type = "VOTE"}}

\* Count of YES votes received
YesVoteCount ==
    Cardinality({m \in msgs : m.type = "VOTE" /\ m.vote = "YES"})

\* Process p receives all votes and decides COMMIT if all YES and no failure detected
DecideCommit(p) ==
    /\ pcState[p] = "VOTED"
    /\ Cardinality({m \in msgs : m.type = "VOTE"}) = N
    /\ \A m \in msgs : m.type = "VOTE" => m.vote = "YES"
    /\ failureDetector[p] = FALSE
    /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
    /\ pcState' = [pcState EXCEPT ![p] = "DECIDED"]
    /\ msgs' = msgs \cup {DecisionMsg("COMMIT")}
    /\ UNCHANGED <<vote, failureDetector, crashed>>

\* Process p decides ABORT due to NO vote or failure detection
DecideAbort(p) ==
    /\ pcState[p] \in {"WORKING", "VOTED"}
    /\ \/ \E m \in msgs : m.type = "VOTE" /\ m.vote = "NO"
       \/ failureDetector[p] = TRUE
       \/ \E m \in msgs : m.type = "DECISION" /\ m.decision = "ABORT"
    /\ decision' = [decision EXCEPT ![p] = "ABORT"]
    /\ pcState' = [pcState EXCEPT ![p] = "DECIDED"]
    /\ msgs' = msgs \cup {DecisionMsg("ABORT")}
    /\ UNCHANGED <<vote, failureDetector, crashed>>

\* Process p receives a COMMIT decision message
ReceiveCommitDecision(p) ==
    /\ pcState[p] = "VOTED"
    /\ \E m \in msgs : m.type = "DECISION" /\ m.decision = "COMMIT"
    /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
    /\ pcState' = [pcState EXCEPT ![p] = "DECIDED"]
    /\ UNCHANGED <<vote, failureDetector, msgs, crashed>>

\* Process p crashes
Crash(p) ==
    /\ pcState[p] # "CRASHED"
    /\ pcState' = [pcState EXCEPT ![p] = "CRASHED"]
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<vote, decision, failureDetector, msgs>>

\* Failure detector at process p nondeterministically detects a crash
DetectFailure(p) ==
    /\ pcState[p] # "CRASHED"
    /\ crashed # {}
    /\ failureDetector' = [failureDetector EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pcState, vote, decision, msgs, crashed>>

\* Combined step for process p
ProcessStep(p) ==
    \/ CastVote(p)
    \/ DecideCommit(p)
    \/ DecideAbort(p)
    \/ ReceiveCommitDecision(p)
    \/ Crash(p)
    \/ DetectFailure(p)

Next ==
    \E p \in Procs : ProcessStep(p)

Spec == Init /\ [][Next]_vars

\* Validity: If all processes vote YES and no process crashes, then COMMIT is possible
AllVotedYes == \A p \in Procs : vote[p] = "YES"
NoCrashes == crashed = {}

Validity ==
    (AllVotedYes /\ NoCrashes /\ (\A p \in Procs : pcState[p] = "DECIDED")) =>
    (\A p \in Procs : decision[p] = "COMMIT")

\* Agreement: No two processes decide differently
Agreement ==
    \A p, q \in Procs :
        (decision[p] \in {"COMMIT", "ABORT"} /\ decision[q] \in {"COMMIT", "ABORT"}) =>
        decision[p] = decision[q]

\* Integrity: A process decides at most once
Integrity ==
    \A p \in Procs : pcState[p] = "DECIDED" => decision[p] # "UNDECIDED"

=============================================================================