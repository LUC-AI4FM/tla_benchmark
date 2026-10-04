-------------------------------- MODULE NBAC --------------------------------

EXTENDS Integers, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

VARIABLES
    vote,           \* vote[p] \in {YES, NO, NONE} - initial vote of process p
    decision,       \* decision[p] \in {COMMIT, ABORT, NONE} - decision of process p
    crashed,        \* crashed[p] \in BOOLEAN - whether process p has crashed
    sent,           \* sent - set of messages that have been sent (pairs <<sender, vote>>)
    received,       \* received[p] - set of messages received by process p
    failureDetector,\* failureDetector[p] \in {CRASHED, ALL_CORRECT} - FD output at p
    voteSent        \* voteSent[p] \in BOOLEAN - whether process p has broadcast its vote

YES == "YES"
NO == "NO"
NONE == "NONE"
COMMIT == "COMMIT"
ABORT == "ABORT"
CRASHED == "CRASHED"
ALL_CORRECT == "ALL_CORRECT"

TypeOK ==
    /\ vote \in [Procs -> {YES, NO, NONE}]
    /\ decision \in [Procs -> {COMMIT, ABORT, NONE}]
    /\ crashed \in [Procs -> BOOLEAN]
    /\ sent \subseteq (Procs \times {YES, NO})
    /\ received \in [Procs -> SUBSET (Procs \times {YES, NO})]
    /\ failureDetector \in [Procs -> {CRASHED, ALL_CORRECT}]
    /\ voteSent \in [Procs -> BOOLEAN]

Init ==
    /\ vote \in [Procs -> {YES, NO}]
    /\ decision = [p \in Procs |-> NONE]
    /\ crashed = [p \in Procs |-> FALSE]
    /\ sent = {}
    /\ received = [p \in Procs |-> {}]
    /\ failureDetector = [p \in Procs |-> ALL_CORRECT]
    /\ voteSent = [p \in Procs |-> FALSE]

BroadcastVote(p) ==
    /\ ~crashed[p]
    /\ ~voteSent[p]
    /\ vote[p] \in {YES, NO}
    /\ sent' = sent \cup {<<p, vote[p]>>}
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, crashed, received, failureDetector>>

ReceiveMessage(p) ==
    /\ ~crashed[p]
    /\ \E msg \in sent :
        /\ msg \notin received[p]
        /\ received' = [received EXCEPT ![p] = received[p] \cup {msg}]
    /\ UNCHANGED <<vote, decision, crashed, sent, failureDetector, voteSent>>

UpdateFailureDetector(p) ==
    /\ ~crashed[p]
    /\ \E fd \in {CRASHED, ALL_CORRECT} :
        failureDetector' = [failureDetector EXCEPT ![p] = fd]
    /\ UNCHANGED <<vote, decision, crashed, sent, received, voteSent>>

ReceivedAllYes(p) ==
    /\ \A q \in Procs : <<q, YES>> \in received[p]

ReceivedAnyNo(p) ==
    \E q \in Procs : <<q, NO>> \in received[p]

DecideCommit(p) ==
    /\ ~crashed[p]
    /\ decision[p] = NONE
    /\ voteSent[p]
    /\ ReceivedAllYes(p)
    /\ failureDetector[p] = ALL_CORRECT
    /\ decision' = [decision EXCEPT ![p] = COMMIT]
    /\ UNCHANGED <<vote, crashed, sent, received, failureDetector, voteSent>>

DecideAbort(p) ==
    /\ ~crashed[p]
    /\ decision[p] = NONE
    /\ voteSent[p]
    /\ \/ failureDetector[p] = CRASHED
       \/ ReceivedAnyNo(p)
    /\ decision' = [decision EXCEPT ![p] = ABORT]
    /\ UNCHANGED <<vote, crashed, sent, received, failureDetector, voteSent>>

Crash(p) ==
    /\ ~crashed[p]
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sent, received, failureDetector, voteSent>>

Next ==
    \/ \E p \in Procs : BroadcastVote(p)
    \/ \E p \in Procs : ReceiveMessage(p)
    \/ \E p \in Procs : UpdateFailureDetector(p)
    \/ \E p \in Procs : DecideCommit(p)
    \/ \E p \in Procs : DecideAbort(p)
    \/ \E p \in Procs : Crash(p)

Fairness ==
    /\ \A p \in Procs : WF_<<vote, decision, crashed, sent, received, failureDetector, voteSent>>(BroadcastVote(p))
    /\ \A p \in Procs : WF_<<vote, decision, crashed, sent, received, failureDetector, voteSent>>(DecideCommit(p))
    /\ \A p \in Procs : WF_<<vote, decision, crashed, sent, received, failureDetector, voteSent>>(DecideAbort(p))
    /\ \A p \in Procs : WF_<<vote, decision, crashed, sent, received, failureDetector, voteSent>>(ReceiveMessage(p))

Spec == Init /\ [][Next]_<<vote, decision, crashed, sent, received, failureDetector, voteSent>> /\ Fairness

Validity ==
    \A p \in Procs :
        decision[p] = COMMIT => \A q \in Procs : vote[q] = YES

ValidityAlt ==
    (\E p \in Procs : vote[p] = NO) => (\A q \in Procs : decision[q] # COMMIT)

ReceivedMonotonic ==
    [][
        \A p \in Procs : received[p] \subseteq received'[p]
    ]_<<received>>

ReceivedSubsetSent ==
    \A p \in Procs : received[p] \subseteq sent

CrashedPermanent ==
    [][
        \A p \in Procs : crashed[p] => crashed'[p]
    ]_<<crashed>>

Safety == TypeOK /\ Validity

EventualDecision ==
    \A p \in Procs : (voteSent[p] /\ ~crashed[p]) ~> (decision[p] # NONE \/ crashed[p])

=============================================================================