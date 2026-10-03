---------------------------- MODULE NBAC ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,           \* Set of processes
    YES,            \* Vote value: YES
    NO              \* Vote value: NO

VARIABLES
    vote,           \* vote[p] = the vote of process p (YES or NO)
    decision,       \* decision[p] = the decision of process p (COMMIT, ABORT, or NONE)
    crashed,        \* crashed[p] = TRUE iff process p has crashed
    failureDetector,\* failureDetector[p] = TRUE iff p's failure detector suspects a crash
    msgs,           \* Set of messages in transit
    pc              \* pc[p] = program counter of process p

\* Decision values
COMMIT == "COMMIT"
ABORT == "ABORT"
NONE == "NONE"

\* Program counter states
INIT_STATE == "init"
VOTED == "voted"
DECIDED == "decided"
CRASHED_STATE == "crashed"

\* Message types
VoteMsg(p, v) == [type |-> "vote", from |-> p, vote |-> v]
DecisionMsg(p, d) == [type |-> "decision", from |-> p, decision |-> d]

TypeOK ==
    /\ vote \in [Proc -> {YES, NO}]
    /\ decision \in [Proc -> {COMMIT, ABORT, NONE}]
    /\ crashed \in [Proc -> BOOLEAN]
    /\ failureDetector \in [Proc -> BOOLEAN]
    /\ pc \in [Proc -> {INIT_STATE, VOTED, DECIDED, CRASHED_STATE}]

Init ==
    /\ vote \in [Proc -> {YES, NO}]  \* Each process has an initial vote
    /\ decision = [p \in Proc |-> NONE]
    /\ crashed = [p \in Proc |-> FALSE]
    /\ failureDetector = [p \in Proc |-> FALSE]
    /\ msgs = {}
    /\ pc = [p \in Proc |-> INIT_STATE]

\* Process p broadcasts its vote
BroadcastVote(p) ==
    /\ pc[p] = INIT_STATE
    /\ ~crashed[p]
    /\ msgs' = msgs \cup {VoteMsg(p, vote[p])}
    /\ pc' = [pc EXCEPT ![p] = VOTED]
    /\ UNCHANGED <<vote, decision, crashed, failureDetector>>

\* Process p receives votes and possibly decides
ReceiveAndDecide(p) ==
    /\ pc[p] = VOTED
    /\ ~crashed[p]
    /\ LET receivedVotes == {m \in msgs : m.type = "vote"}
           votingProcs == {m.from : m \in receivedVotes}
           allVotesReceived == Proc \subseteq votingProcs
           allYes == \A m \in receivedVotes : m.vote = YES
           noSuspectedFailure == ~failureDetector[p]
       IN
       \/ \* Can commit if all voted YES and no failure suspected
          /\ allVotesReceived
          /\ allYes
          /\ noSuspectedFailure
          /\ decision' = [decision EXCEPT ![p] = COMMIT]
          /\ msgs' = msgs \cup {DecisionMsg(p, COMMIT)}
          /\ pc' = [pc EXCEPT ![p] = DECIDED]
          /\ UNCHANGED <<vote, crashed, failureDetector>>
       \/ \* Must abort if some vote is NO
          /\ allVotesReceived
          /\ ~allYes
          /\ decision' = [decision EXCEPT ![p] = ABORT]
          /\ msgs' = msgs \cup {DecisionMsg(p, ABORT)}
          /\ pc' = [pc EXCEPT ![p] = DECIDED]
          /\ UNCHANGED <<vote, crashed, failureDetector>>
       \/ \* Abort if failure detector suspects a crash
          /\ failureDetector[p]
          /\ decision' = [decision EXCEPT ![p] = ABORT]
          /\ msgs' = msgs \cup {DecisionMsg(p, ABORT)}
          /\ pc' = [pc EXCEPT ![p] = DECIDED]
          /\ UNCHANGED <<vote, crashed, failureDetector>>

\* Process p receives a decision message and adopts it
ReceiveDecision(p) ==
    /\ pc[p] \in {VOTED, INIT_STATE}
    /\ ~crashed[p]
    /\ \E m \in msgs :
        /\ m.type = "decision"
        /\ decision' = [decision EXCEPT ![p] = m.decision]
        /\ pc' = [pc EXCEPT ![p] = DECIDED]
        /\ UNCHANGED <<vote, crashed, failureDetector, msgs>>

\* Process p crashes
Crash(p) ==
    /\ ~crashed[p]
    /\ pc[p] # CRASHED_STATE
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ pc' = [pc EXCEPT ![p] = CRASHED_STATE]
    /\ UNCHANGED <<vote, decision, failureDetector, msgs>>

\* Failure detector at process p nondeterministically detects a crash
UpdateFailureDetector(p) ==
    /\ ~crashed[p]
    /\ pc[p] # CRASHED_STATE
    /\ \E q \in Proc : crashed[q]  \* There is actually a crashed process
    /\ failureDetector' = [failureDetector EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, crashed, msgs, pc>>

\* Failure detector can also spuriously suspect (for completeness of nondeterminism)
SpuriousSuspicion(p) ==
    /\ ~crashed[p]
    /\ pc[p] # CRASHED_STATE
    /\ failureDetector' = [failureDetector EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, crashed, msgs, pc>>

\* Combined step for process p
ProcessStep(p) ==
    \/ BroadcastVote(p)
    \/ ReceiveAndDecide(p)
    \/ ReceiveDecision(p)
    \/ Crash(p)
    \/ UpdateFailureDetector(p)

Next ==
    \E p \in Proc : ProcessStep(p)

\* Fairness: weak fairness on non-crashed process steps
Fairness ==
    \A p \in Proc : WF_<<vote, decision, crashed, failureDetector, msgs, pc>>(ProcessStep(p) /\ ~crashed[p])

Spec == Init /\ [][Next]_<<vote, decision, crashed, failureDetector, msgs, pc>> /\ Fairness

\* Safety Invariants

\* Agreement: No two processes decide differently
Agreement ==
    \A p, q \in Proc :
        (decision[p] # NONE /\ decision[q] # NONE) => (decision[p] = decision[q])

\* Validity: If all processes vote YES and no process crashes, then ABORT is not decided
\* Equivalently: If some process decides COMMIT, then all processes voted YES
ValidityCommit ==
    \A p \in Proc :
        decision[p] = COMMIT => \A q \in Proc : vote[q] = YES

\* Validity: If some process votes NO, then COMMIT cannot be decided
ValidityAbort ==
    (\E p \in Proc : vote[p] = NO) => 
        \A q \in Proc : decision[q] # COMMIT

\* If all vote YES and none crashed, COMMIT is possible (not ABORT forced)
ValidityAllYesNoCrash ==
    ((\A p \in Proc : vote[p] = YES) /\ (\A p \in Proc : ~crashed[p])) =>
        ~(\E p \in Proc : decision[p] = ABORT /\ \A q \in Proc : ~crashed[q])

\* Integrity: A process decides at most once
Integrity ==
    \A p \in Proc :
        pc[p] = DECIDED => decision[p] # NONE

\* Non-triviality: COMMIT can only be decided if all voted YES
NonTriviality ==
    \A p \in Proc :
        decision[p] = COMMIT => \A q \in Proc : vote[q] = YES

\* Liveness Properties

\* Termination: If no process crashes and failure detector is accurate,
\* then all processes eventually decide
Termination ==
    (\A p \in Proc : ~crashed[p]) ~> (\A p \in Proc : decision[p] # NONE)

\* Non-blocking: If a process has crashed, non-crashed processes can still decide
NonBlocking ==
    \A p \in Proc :
        (~crashed[p] /\ pc[p] # CRASHED_STATE) ~> 
            (crashed[p] \/ decision[p] # NONE)

=============================================================================