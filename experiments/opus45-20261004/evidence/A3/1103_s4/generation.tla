--------------------------- MODULE NBAC ---------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    Proc,           \* Set of processes
    YES,            \* Vote value YES
    NO              \* Vote value NO

VARIABLES
    vote,           \* vote[p] = the vote of process p (YES or NO)
    decision,       \* decision[p] = the decision of process p (COMMIT, ABORT, or NONE)
    crashed,        \* crashed[p] = TRUE iff process p has crashed
    suspected,      \* suspected[p] = set of processes that p suspects have crashed
    msgs            \* msgs[p] = set of messages received by process p

\* Decision values
COMMIT == "COMMIT"
ABORT == "ABORT"
NONE == "NONE"

\* Message types
VoteMsg(p, v) == [type |-> "VOTE", sender |-> p, val |-> v]
DecisionMsg(p, d) == [type |-> "DECISION", sender |-> p, val |-> d]

\* Type definitions
VoteType == {YES, NO}
DecisionType == {COMMIT, ABORT, NONE}
MsgType == [type: {"VOTE"}, sender: Proc, val: VoteType] \cup
           [type: {"DECISION"}, sender: Proc, val: {COMMIT, ABORT}]

TypeOK ==
    /\ vote \in [Proc -> VoteType]
    /\ decision \in [Proc -> DecisionType]
    /\ crashed \in [Proc -> BOOLEAN]
    /\ suspected \in [Proc -> SUBSET Proc]
    /\ msgs \in [Proc -> SUBSET MsgType]

\* Helper: Get all vote messages received by process p
ReceivedVotes(p) == {m \in msgs[p] : m.type = "VOTE"}

\* Helper: Get all decision messages received by process p
ReceivedDecisions(p) == {m \in msgs[p] : m.type = "DECISION"}

\* Helper: Check if p has received votes from all processes
HasAllVotes(p) == {m.sender : m \in ReceivedVotes(p)} = Proc

\* Helper: Check if all received votes are YES
AllVotesYes(p) == \A m \in ReceivedVotes(p) : m.val = YES

\* Initial state
Init ==
    /\ vote \in [Proc -> VoteType]
    /\ decision = [p \in Proc |-> NONE]
    /\ crashed = [p \in Proc |-> FALSE]
    /\ suspected = [p \in Proc |-> {}]
    /\ msgs = [p \in Proc |-> {}]

\* Process p broadcasts its vote
BroadcastVote(p) ==
    /\ ~crashed[p]
    /\ decision[p] = NONE
    /\ msgs' = [q \in Proc |-> 
                    IF ~crashed[q] 
                    THEN msgs[q] \cup {VoteMsg(p, vote[p])}
                    ELSE msgs[q]]
    /\ UNCHANGED <<vote, decision, crashed, suspected>>

\* Process p broadcasts a decision
BroadcastDecision(p, d) ==
    msgs' = [q \in Proc |-> 
                IF ~crashed[q]
                THEN msgs[q] \cup {DecisionMsg(p, d)}
                ELSE msgs[q]]

\* Process p decides COMMIT (received all YES votes, no suspicions)
DecideCommit(p) ==
    /\ ~crashed[p]
    /\ decision[p] = NONE
    /\ HasAllVotes(p)
    /\ AllVotesYes(p)
    /\ suspected[p] = {}
    /\ decision' = [decision EXCEPT ![p] = COMMIT]
    /\ BroadcastDecision(p, COMMIT)
    /\ UNCHANGED <<vote, crashed, suspected>>

\* Process p decides ABORT (received NO vote or suspects someone)
DecideAbortOnNo(p) ==
    /\ ~crashed[p]
    /\ decision[p] = NONE
    /\ \E m \in ReceivedVotes(p) : m.val = NO
    /\ decision' = [decision EXCEPT ![p] = ABORT]
    /\ BroadcastDecision(p, ABORT)
    /\ UNCHANGED <<vote, crashed, suspected>>

DecideAbortOnSuspicion(p) ==
    /\ ~crashed[p]
    /\ decision[p] = NONE
    /\ suspected[p] /= {}
    /\ decision' = [decision EXCEPT ![p] = ABORT]
    /\ BroadcastDecision(p, ABORT)
    /\ UNCHANGED <<vote, crashed, suspected>>

\* Process p adopts a decision from a received decision message
AdoptDecision(p) ==
    /\ ~crashed[p]
    /\ decision[p] = NONE
    /\ \E m \in ReceivedDecisions(p) : 
        /\ decision' = [decision EXCEPT ![p] = m.val]
        /\ BroadcastDecision(p, m.val)
    /\ UNCHANGED <<vote, crashed, suspected>>

\* Failure detector update: process p suspects process q
Suspect(p, q) ==
    /\ ~crashed[p]
    /\ p /= q
    /\ crashed[q]  \* Only suspect actually crashed processes (strong completeness)
    /\ suspected' = [suspected EXCEPT ![p] = suspected[p] \cup {q}]
    /\ UNCHANGED <<vote, decision, crashed, msgs>>

\* Failure detector may also nondeterministically suspect (weak accuracy relaxation)
SuspectNondet(p, q) ==
    /\ ~crashed[p]
    /\ p /= q
    /\ suspected' = [suspected EXCEPT ![p] = suspected[p] \cup {q}]
    /\ UNCHANGED <<vote, decision, crashed, msgs>>

\* Process p crashes
Crash(p) ==
    /\ ~crashed[p]
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, suspected, msgs>>

\* Combined process step
ProcessStep(p) ==
    \/ BroadcastVote(p)
    \/ DecideCommit(p)
    \/ DecideAbortOnNo(p)
    \/ DecideAbortOnSuspicion(p)
    \/ AdoptDecision(p)
    \/ \E q \in Proc : Suspect(p, q)
    \/ \E q \in Proc : SuspectNondet(p, q)

\* Next state relation
Next ==
    \/ \E p \in Proc : ProcessStep(p)
    \/ \E p \in Proc : Crash(p)

\* Fairness: weak fairness on process steps for non-crashed processes
Fairness ==
    \A p \in Proc : WF_<<vote, decision, crashed, suspected, msgs>>(ProcessStep(p))

\* Specification
Spec == Init /\ [][Next]_<<vote, decision, crashed, suspected, msgs>> /\ Fairness

\* -------------- SAFETY INVARIANTS --------------

\* Agreement: No two processes decide differently
Agreement ==
    \A p, q \in Proc :
        (decision[p] /= NONE /\ decision[q] /= NONE) =>
            decision[p] = decision[q]

\* Validity: If all processes vote YES and no process crashes, 
\* then ABORT cannot be decided
Validity ==
    (\A p \in Proc : vote[p] = YES) /\
    (\A p \in Proc : ~crashed[p]) =>
        \A q \in Proc : decision[q] /= ABORT

\* Integrity: A process decides at most once
Integrity ==
    \A p \in Proc :
        decision[p] /= NONE =>
            [][decision[p] = decision'[p]]_<<decision>>

\* If any process votes NO, no process can decide COMMIT
NoCommitOnNo ==
    (\E p \in Proc : vote[p] = NO) =>
        \A q \in Proc : decision[q] /= COMMIT

\* If any process crashes, and this is detected, COMMIT should not happen
\* (This captures the non-blocking aspect with crash detection)
CrashSafety ==
    \A p \in Proc :
        (crashed[p] /\ \E q \in Proc : p \in suspected[q]) =>
            \A r \in Proc : decision[r] /= COMMIT \/ decision[r] = NONE

\* -------------- LIVENESS PROPERTIES --------------

\* Termination: Every correct (non-crashed) process eventually decides
Termination ==
    \A p \in Proc : 
        (~crashed[p]) ~> (decision[p] /= NONE \/ crashed[p])

\* Non-triviality: If all vote YES and no one crashes, COMMIT is possible
NonTriviality ==
    ((\A p \in Proc : vote[p] = YES) /\ 
     [](\A p \in Proc : ~crashed[p])) ~>
        (\E p \in Proc : decision[p] = COMMIT)

=============================================================================