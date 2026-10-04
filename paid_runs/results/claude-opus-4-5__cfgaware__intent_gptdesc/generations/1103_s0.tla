-------------------------------- MODULE NBAC --------------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

VARIABLES
    vote,           \* vote[p] \in {"YES", "NO"} - initial vote of process p
    crashed,        \* crashed[p] \in BOOLEAN - whether process p has crashed
    decision,       \* decision[p] \in {"COMMIT", "ABORT", "UNDECIDED"} - decision of process p
    sent,           \* sent[p] \in SUBSET Procs - processes to which p has sent its vote
    received,       \* received[p] \in [Procs -> {"YES", "NO", "NONE"}] - votes received by p
    suspected,      \* suspected[p] \in SUBSET Procs - processes that p suspects have crashed
    msgs            \* msgs \in SUBSET (Procs \times Procs \times {"YES", "NO"}) - messages in transit

vars == <<vote, crashed, decision, sent, received, suspected, msgs>>

\* Type invariant
TypeOK ==
    /\ vote \in [Procs -> {"YES", "NO"}]
    /\ crashed \in [Procs -> BOOLEAN]
    /\ decision \in [Procs -> {"COMMIT", "ABORT", "UNDECIDED"}]
    /\ sent \in [Procs -> SUBSET Procs]
    /\ received \in [Procs -> [Procs -> {"YES", "NO", "NONE"}]]
    /\ suspected \in [Procs -> SUBSET Procs]
    /\ msgs \subseteq (Procs \times Procs \times {"YES", "NO"})

\* Initial state: processes vote YES or NO, nothing sent/received, no crashes, no decisions
Init ==
    /\ vote \in [Procs -> {"YES", "NO"}]
    /\ crashed = [p \in Procs |-> FALSE]
    /\ decision = [p \in Procs |-> "UNDECIDED"]
    /\ sent = [p \in Procs |-> {}]
    /\ received = [p \in Procs |-> [q \in Procs |-> IF q = p THEN vote[p] ELSE "NONE"]]
    /\ suspected = [p \in Procs |-> {}]
    /\ msgs = {}

\* Process p sends its vote to process q
SendVote(p, q) ==
    /\ ~crashed[p]
    /\ q \notin sent[p]
    /\ sent' = [sent EXCEPT ![p] = sent[p] \cup {q}]
    /\ msgs' = msgs \cup {<<p, q, vote[p]>>}
    /\ UNCHANGED <<vote, crashed, decision, received, suspected>>

\* Process p receives a message from process q
ReceiveVote(p, q, v) ==
    /\ ~crashed[p]
    /\ <<q, p, v>> \in msgs
    /\ received[p][q] = "NONE"
    /\ received' = [received EXCEPT ![p][q] = v]
    /\ msgs' = msgs \ {<<q, p, v>>}
    /\ UNCHANGED <<vote, crashed, decision, sent, suspected>>

\* Process p crashes (irreversible)
Crash(p) ==
    /\ ~crashed[p]
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sent, received, suspected, msgs>>

\* Failure detector update: process p's view of suspected processes changes
\* The failure detector is unreliable - it can suspect anyone (including live processes)
\* and can stop suspecting crashed processes
UpdateSuspicion(p) ==
    /\ ~crashed[p]
    /\ \E newSuspected \in SUBSET Procs:
        /\ suspected' = [suspected EXCEPT ![p] = newSuspected]
    /\ UNCHANGED <<vote, crashed, decision, sent, received, msgs>>

\* Helper: check if process p has received all votes
ReceivedAllVotes(p) ==
    \A q \in Procs: received[p][q] # "NONE"

\* Helper: check if all received votes are YES
AllReceivedYes(p) ==
    \A q \in Procs: received[p][q] = "YES"

\* Helper: check if any received vote is NO
SomeReceivedNo(p) ==
    \E q \in Procs: received[p][q] = "NO"

\* Helper: processes that p is waiting for (not received and not suspected)
WaitingFor(p) ==
    {q \in Procs: received[p][q] = "NONE" /\ q \notin suspected[p]}

\* Process p decides COMMIT
\* Can only commit if received all YES votes and no one is suspected
DecideCommit(p) ==
    /\ ~crashed[p]
    /\ decision[p] = "UNDECIDED"
    /\ ReceivedAllVotes(p)
    /\ AllReceivedYes(p)
    /\ suspected[p] = {}
    /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
    /\ UNCHANGED <<vote, crashed, sent, received, suspected, msgs>>

\* Process p decides ABORT
\* Abort if received NO or if someone is suspected and we can't wait anymore
DecideAbort(p) ==
    /\ ~crashed[p]
    /\ decision[p] = "UNDECIDED"
    /\ \/ SomeReceivedNo(p)
       \/ /\ suspected[p] # {}
          /\ WaitingFor(p) = {}
    /\ decision' = [decision EXCEPT ![p] = "ABORT"]
    /\ UNCHANGED <<vote, crashed, sent, received, suspected, msgs>>

\* Next state relation
Next ==
    \/ \E p, q \in Procs: SendVote(p, q)
    \/ \E p \in Procs, q \in Procs, v \in {"YES", "NO"}: ReceiveVote(p, q, v)
    \/ \E p \in Procs: Crash(p)
    \/ \E p \in Procs: UpdateSuspicion(p)
    \/ \E p \in Procs: DecideCommit(p)
    \/ \E p \in Procs: DecideAbort(p)

\* Fairness conditions
\* Weak fairness on message delivery and decision actions
Fairness ==
    /\ \A p, q \in Procs: WF_vars(SendVote(p, q))
    /\ \A p \in Procs, q \in Procs, v \in {"YES", "NO"}: WF_vars(ReceiveVote(p, q, v))
    /\ \A p \in Procs: WF_vars(DecideCommit(p))
    /\ \A p \in Procs: WF_vars(DecideAbort(p))

\* Complete specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* ============================================================================