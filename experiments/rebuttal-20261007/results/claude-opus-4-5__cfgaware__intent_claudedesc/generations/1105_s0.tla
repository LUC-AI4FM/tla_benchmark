---------------------------- MODULE NBAC ----------------------------

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANT N

VARIABLES
    vote,           \* vote[p] = "YES" or "NO" - initial vote of process p
    sent,           \* sent[p] = TRUE if process p has broadcast its vote
    received,       \* received[p] = set of processes from which p has received votes
    receivedVotes,  \* receivedVotes[p] = function from received processes to their votes
    decision,       \* decision[p] = "COMMIT", "ABORT", or "NONE"
    crashed,        \* crashed[p] = TRUE if process p has crashed
    suspected,      \* suspected[p] = set of processes that p suspects
    msgs            \* msgs = set of messages in transit {[from |-> p, vote |-> v]}

Procs == 1..N

Votes == {"YES", "NO"}
Decisions == {"COMMIT", "ABORT", "NONE"}

TypeOK ==
    /\ vote \in [Procs -> Votes]
    /\ sent \in [Procs -> BOOLEAN]
    /\ received \in [Procs -> SUBSET Procs]
    /\ receivedVotes \in [Procs -> [SUBSET Procs -> Votes \cup {""}]]
    /\ decision \in [Procs -> Decisions]
    /\ crashed \in [Procs -> BOOLEAN]
    /\ suspected \in [Procs -> SUBSET Procs]
    /\ msgs \subseteq [from : Procs, vote : Votes]

\* Helper to check if receivedVotes is valid
ReceivedVotesTypeOK ==
    \A p \in Procs : 
        \A q \in Procs :
            IF q \in received[p] 
            THEN receivedVotes[p][q] \in Votes
            ELSE TRUE

\* Initialization with arbitrary votes
InitArbitrary ==
    /\ vote \in [Procs -> Votes]
    /\ sent = [p \in Procs |-> FALSE]
    /\ received = [p \in Procs |-> {}]
    /\ receivedVotes = [p \in Procs |-> [q \in SUBSET Procs |-> ""]]
    /\ decision = [p \in Procs |-> "NONE"]
    /\ crashed = [p \in Procs |-> FALSE]
    /\ suspected = [p \in Procs |-> {}]
    /\ msgs = {}

\* Initialization with all YES votes
InitAllYes ==
    /\ vote = [p \in Procs |-> "YES"]
    /\ sent = [p \in Procs |-> FALSE]
    /\ received = [p \in Procs |-> {}]
    /\ receivedVotes = [p \in Procs |-> [q \in SUBSET Procs |-> ""]]
    /\ decision = [p \in Procs |-> "NONE"]
    /\ crashed = [p \in Procs |-> FALSE]
    /\ suspected = [p \in Procs |-> {}]
    /\ msgs = {}

\* Initialization with all NO votes
InitAllNo ==
    /\ vote = [p \in Procs |-> "NO"]
    /\ sent = [p \in Procs |-> FALSE]
    /\ received = [p \in Procs |-> {}]
    /\ receivedVotes = [p \in Procs |-> [q \in SUBSET Procs |-> ""]]
    /\ decision = [p \in Procs |-> "NONE"]
    /\ crashed = [p \in Procs |-> FALSE]
    /\ suspected = [p \in Procs |-> {}]
    /\ msgs = {}

\* Use arbitrary initialization as default
Init == InitArbitrary

\* Process p broadcasts its vote
Broadcast(p) ==
    /\ ~crashed[p]
    /\ ~sent[p]
    /\ sent' = [sent EXCEPT ![p] = TRUE]
    /\ msgs' = msgs \cup {[from |-> p, vote |-> vote[p]]}
    /\ UNCHANGED <<vote, received, receivedVotes, decision, crashed, suspected>>

\* Process p receives a vote from process q
Receive(p, m) ==
    /\ ~crashed[p]
    /\ sent[p]
    /\ m \in msgs
    /\ m.from \notin received[p]
    /\ decision[p] = "NONE"
    /\ received' = [received EXCEPT ![p] = received[p] \cup {m.from}]
    /\ receivedVotes' = [receivedVotes EXCEPT ![p] = [receivedVotes[p] EXCEPT ![{m.from}] = m.vote,
                                                                              ![received[p] \cup {m.from}] = m.vote]]
    /\ UNCHANGED <<vote, sent, decision, crashed, suspected, msgs>>

\* Process p decides to ABORT due to suspecting some process or receiving NO
DecideAbort(p) ==
    /\ ~crashed[p]
    /\ sent[p]
    /\ decision[p] = "NONE"
    /\ \/ suspected[p] /= {}
       \/ \E m \in msgs : m.from \in received[p] /\ m.vote = "NO"
       \/ \E q \in received[p] : \E m \in msgs : m.from = q /\ m.vote = "NO"
    /\ decision' = [decision EXCEPT ![p] = "ABORT"]
    /\ UNCHANGED <<vote, sent, received, receivedVotes, crashed, suspected, msgs>>

\* Process p decides to COMMIT (received YES from all N processes)
DecideCommit(p) ==
    /\ ~crashed[p]
    /\ sent[p]
    /\ decision[p] = "NONE"
    /\ suspected[p] = {}
    /\ received[p] = Procs
    /\ \A m \in msgs : m.from \in Procs => m.vote = "YES"
    /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
    /\ UNCHANGED <<vote, sent, received, receivedVotes, crashed, suspected, msgs>>

\* Process p crashes
Crash(p) ==
    /\ ~crashed[p]
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, sent, received, receivedVotes, decision, suspected, msgs>>

\* Failure detector at process p suspects process q
Suspect(p, q) ==
    /\ ~crashed[p]
    /\ p /= q
    /\ q \notin suspected[p]
    /\ suspected' = [suspected EXCEPT ![p] = suspected[p] \cup {q}]
    /\ UNCHANGED <<vote, sent, received, receivedVotes, decision, crashed, msgs>>

\* Non-crash actions for fairness
NonCrashAction(p) ==
    \/ Broadcast(p)
    \/ \E m \in msgs : Receive(p, m)
    \/ DecideAbort(p)
    \/ DecideCommit(p)

Next ==
    \/ \E p \in Procs : Broadcast(p)
    \/ \E p \in Procs : \E m \in msgs : Receive(p, m)
    \/ \E p \in Procs : DecideAbort(p)
    \/ \E p \in Procs : DecideCommit(p)
    \/ \E p \in Procs : Crash(p)
    \/ \E p \in Procs : \E q \in Procs : Suspect(p, q)

\* Fairness: weak fairness on non-crash actions
Fairness ==
    \A p \in Procs : WF_<<vote, sent, received, receivedVotes, decision, crashed, suspected, msgs>>(NonCrashAction(p))

Spec == Init /\ [][Next]_<<vote, sent, received, receivedVotes, decision, crashed, suspected, msgs>> /\ Fairness

\* A process is correct if it never crashes
Correct(p) == ~crashed[p]

\* Agreement: no two correct processes decide differently
Agreement ==
    ~(\E p, q \in Procs : 
        /\ ~crashed[p] 
        /\ ~crashed[q] 
        /\ decision[p] = "COMMIT" 
        /\ decision[q] = "ABORT")

AgrrLtl == []Agreement

\* Abort validity: if any process votes NO, no process commits
AbortValidity ==
    (\E p \in Procs : vote[p] = "NO") => 
    (\A q \in Procs : decision[q] /= "COMMIT")

AbortValidityLtl == []AbortValidity

\* Commit validity: if all vote YES and none suspected, no abort
CommitValidity ==
    ((\A p \in Procs : vote[p] = "YES") /\ (\A p \in Procs : suspected[p] = {})) =>
    (\A q \in Procs : ~crashed[q] => decision[q] /= "ABORT")

CommitValidityLtl == []CommitValidity

\* Termination: if no crashes and no suspicions, everyone eventually decides
NoFailures == 
    /\ \A p \in Procs : ~crashed[p]
    /\ \A p \in Procs : suspected[p] = {}

AllDecided == \A p \in Procs : decision[p] /= "NONE"

TerminationLtl == 
    ([]NoFailures) => <>AllDecided

=============================================================================