------------------------------ MODULE NBAC ------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    Procs,          \* Set of process identifiers
    YES,            \* Vote value: YES
    NO              \* Vote value: NO

VARIABLES
    vote,           \* vote[p] = the vote of process p (YES or NO)
    decision,       \* decision[p] = the decision of process p (COMMIT, ABORT, or NONE)
    crashed,        \* crashed[p] = TRUE iff process p has crashed
    failureDetector,\* failureDetector[p] = TRUE iff p's detector reports some crash
    msgs            \* Set of messages in transit

\* Decision values
NONE == "NONE"
COMMIT == "COMMIT"
ABORT == "ABORT"

\* Message types
VoteMsg == "VOTE"
DecisionMsg == "DECISION"

\* Type definitions
VoteValue == {YES, NO}
DecisionValue == {NONE, COMMIT, ABORT}

Message == 
    [type: {VoteMsg}, src: Procs, vote: VoteValue] \cup
    [type: {DecisionMsg}, src: Procs, decision: {COMMIT, ABORT}]

TypeOK ==
    /\ vote \in [Procs -> VoteValue]
    /\ decision \in [Procs -> DecisionValue]
    /\ crashed \in [Procs -> BOOLEAN]
    /\ failureDetector \in [Procs -> BOOLEAN]
    /\ msgs \subseteq Message

\* Initial state
Init ==
    /\ vote \in [Procs -> VoteValue]  \* Each process has an initial vote
    /\ decision = [p \in Procs |-> NONE]
    /\ crashed = [p \in Procs |-> FALSE]
    /\ failureDetector = [p \in Procs |-> FALSE]
    /\ msgs = {}

\* Process p broadcasts its vote
BroadcastVote(p) ==
    /\ ~crashed[p]
    /\ decision[p] = NONE
    /\ msgs' = msgs \cup {[type |-> VoteMsg, src |-> p, vote |-> vote[p]]}
    /\ UNCHANGED <<vote, decision, crashed, failureDetector>>

\* Process p receives votes and makes a decision
ReceiveAndDecide(p) ==
    /\ ~crashed[p]
    /\ decision[p] = NONE
    /\ LET voteMessages == {m \in msgs : m.type = VoteMsg}
           receivedVotes == {m.vote : m \in voteMessages}
           voteSenders == {m.src : m \in voteMessages}
       IN
       \* If we have votes from all processes and all voted YES and no failure detected
       \/ /\ voteSenders = Procs
          /\ receivedVotes = {YES}
          /\ ~failureDetector[p]
          /\ decision' = [decision EXCEPT ![p] = COMMIT]
          /\ msgs' = msgs \cup {[type |-> DecisionMsg, src |-> p, decision |-> COMMIT]}
          /\ UNCHANGED <<vote, crashed, failureDetector>>
       \* If we detected a failure or received a NO vote, abort
       \/ /\ \/ failureDetector[p]
             \/ NO \in receivedVotes
          /\ decision' = [decision EXCEPT ![p] = ABORT]
          /\ msgs' = msgs \cup {[type |-> DecisionMsg, src |-> p, decision |-> ABORT]}
          /\ UNCHANGED <<vote, crashed, failureDetector>>

\* Process p receives a decision message and adopts it
ReceiveDecision(p) ==
    /\ ~crashed[p]
    /\ decision[p] = NONE
    /\ \E m \in msgs :
        /\ m.type = DecisionMsg
        /\ decision' = [decision EXCEPT ![p] = m.decision]
        /\ UNCHANGED <<vote, crashed, failureDetector, msgs>>

\* Process p crashes
Crash(p) ==
    /\ ~crashed[p]
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, failureDetector, msgs>>

\* Failure detector at process p detects a crash (may be accurate or inaccurate)
\* Models unreliable failure detector that can nondeterministically report crashes
FailureDetectorUpdate(p) ==
    /\ ~crashed[p]
    /\ \/ /\ \E q \in Procs : crashed[q]  \* There is an actual crash
          /\ failureDetector' = [failureDetector EXCEPT ![p] = TRUE]
       \/ /\ failureDetector' = [failureDetector EXCEPT ![p] = TRUE]  \* Nondeterministic suspicion
    /\ UNCHANGED <<vote, decision, crashed, msgs>>

\* Combined step for process p
ProcessStep(p) ==
    \/ BroadcastVote(p)
    \/ ReceiveAndDecide(p)
    \/ ReceiveDecision(p)
    \/ FailureDetectorUpdate(p)

\* Next state relation
Next ==
    \/ \E p \in Procs : ProcessStep(p)
    \/ \E p \in Procs : Crash(p)

\* Fairness: weak fairness on process steps for non-crashed processes
Fairness ==
    /\ \A p \in Procs : WF_<<vote, decision, crashed, failureDetector, msgs>>(ProcessStep(p))

\* Complete specification
Spec == Init /\ [][Next]_<<vote, decision, crashed, failureDetector, msgs>> /\ Fairness

--------------------------------------------------------------------------------
\* Safety Invariants
--------------------------------------------------------------------------------

\* Agreement: No two processes decide differently
Agreement ==
    \A p, q \in Procs :
        (decision[p] \in {COMMIT, ABORT} /\ decision[q] \in {COMMIT, ABORT})
        => decision[p] = decision[q]

\* Validity 1: If a process decides COMMIT, then all processes voted YES
ValidityCommit ==
    \A p \in Procs :
        decision[p] = COMMIT => \A q \in Procs : vote[q] = YES

\* Validity 2: If a process decides ABORT, then either some process voted NO
\* or some process crashed
ValidityAbort ==
    \A p \in Procs :
        decision[p] = ABORT =>
            \/ \E q \in Procs : vote[q] = NO
            \/ \E q \in Procs : crashed[q]

\* Combined validity condition
Validity == ValidityCommit /\ ValidityAbort

\* Integrity: A process decides at most once (implicit in the model since
\* decision only changes from NONE to COMMIT or ABORT)
Integrity ==
    \A p \in Procs :
        decision[p] \in {COMMIT, ABORT} =>
            [][decision[p] = decision'[p]]_<<decision>>

\* Non-triviality: If all processes vote YES and no process crashes,
\* then ABORT should not be decided
NonTrivialityCondition ==
    (\A p \in Procs : vote[p] = YES) /\ (\A p \in Procs : ~crashed[p])

NonTriviality ==
    NonTrivialityCondition =>
        \A p \in Procs : decision[p] # ABORT \/ crashed[p]

\* All safety invariants combined
SafetyInvariant ==
    /\ TypeOK
    /\ Agreement
    /\ Validity

--------------------------------------------------------------------------------
\* Liveness Properties
--------------------------------------------------------------------------------

\* Termination: If no process crashes, every process eventually decides
\* (under fairness assumptions)
Termination ==
    (\A p \in Procs : ~crashed[p]) ~>
        (\A p \in Procs : decision[p] \in {COMMIT, ABORT})

\* Non-blocking: If a correct process exists, it eventually decides
NonBlocking ==
    \A p \in Procs :
        (~crashed[p]) ~> (decision[p] \in {COMMIT, ABORT} \/ crashed[p])

================================================================================