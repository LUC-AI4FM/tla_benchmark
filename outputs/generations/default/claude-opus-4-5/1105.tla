---------------------------- MODULE nbac ----------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
    Proc,           \* Set of processes
    AllYes,         \* Boolean: if TRUE, all processes initially vote YES; if FALSE, all vote NO
    MaxSuspected    \* Maximum number of processes that can be suspected

VARIABLES
    vote,           \* vote[p] = "YES" or "NO" - initial vote of process p
    crashed,        \* crashed[p] = TRUE if process p has crashed
    suspected,      \* suspected[p] = TRUE if process p is suspected by failure detector
    decision,       \* decision[p] = "COMMIT", "ABORT", or "NONE" - decision of process p
    msgs,           \* Set of messages in transit
    received,       \* received[p] = set of messages received by process p
    phase           \* phase[p] = current phase of process p

vars == <<vote, crashed, suspected, decision, msgs, received, phase>>

\* Message types
Message == [type: {"VOTE", "DECISION"}, 
            from: Proc, 
            content: {"YES", "NO", "COMMIT", "ABORT"}]

\* Type invariant
TypeOK ==
    /\ vote \in [Proc -> {"YES", "NO"}]
    /\ crashed \in [Proc -> BOOLEAN]
    /\ suspected \in [Proc -> BOOLEAN]
    /\ decision \in [Proc -> {"COMMIT", "ABORT", "NONE"}]
    /\ msgs \subseteq Message
    /\ received \in [Proc -> SUBSET Message]
    /\ phase \in [Proc -> {"INIT", "VOTED", "DECIDED"}]

\* Initial state - all processes vote YES or all vote NO based on AllYes constant
Init ==
    /\ vote = [p \in Proc |-> IF AllYes THEN "YES" ELSE "NO"]
    /\ crashed = [p \in Proc |-> FALSE]
    /\ suspected = [p \in Proc |-> FALSE]
    /\ decision = [p \in Proc |-> "NONE"]
    /\ msgs = {}
    /\ received = [p \in Proc |-> {}]
    /\ phase = [p \in Proc |-> "INIT"]

\* Process p sends its vote to all other processes
SendVote(p) ==
    /\ ~crashed[p]
    /\ phase[p] = "INIT"
    /\ msgs' = msgs \cup {[type |-> "VOTE", from |-> p, content |-> vote[p]]}
    /\ phase' = [phase EXCEPT ![p] = "VOTED"]
    /\ UNCHANGED <<vote, crashed, suspected, decision, received>>

\* Process p receives a message m
ReceiveMessage(p, m) ==
    /\ ~crashed[p]
    /\ m \in msgs
    /\ m \notin received[p]
    /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
    /\ UNCHANGED <<vote, crashed, suspected, decision, msgs, phase>>

\* Check if process p has received votes from all non-suspected processes
ReceivedAllVotes(p) ==
    \A q \in Proc : 
        q = p \/ suspected[q] \/ 
        \E m \in received[p] : m.type = "VOTE" /\ m.from = q

\* Check if all received votes are YES
AllReceivedYes(p) ==
    /\ vote[p] = "YES"
    /\ \A m \in received[p] : m.type = "VOTE" => m.content = "YES"

\* Check if any process is suspected or voted NO
ShouldAbort(p) ==
    \/ vote[p] = "NO"
    \/ \E m \in received[p] : m.type = "VOTE" /\ m.content = "NO"
    \/ \E q \in Proc : suspected[q]

\* Process p decides to commit
DecideCommit(p) ==
    /\ ~crashed[p]
    /\ phase[p] = "VOTED"
    /\ decision[p] = "NONE"
    /\ ReceivedAllVotes(p)
    /\ AllReceivedYes(p)
    /\ ~ShouldAbort(p)
    /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
    /\ msgs' = msgs \cup {[type |-> "DECISION", from |-> p, content |-> "COMMIT"]}
    /\ phase' = [phase EXCEPT ![p] = "DECIDED"]
    /\ UNCHANGED <<vote, crashed, suspected, received>>

\* Process p decides to abort
DecideAbort(p) ==
    /\ ~crashed[p]
    /\ phase[p] \in {"INIT", "VOTED"}
    /\ decision[p] = "NONE"
    /\ \/ ShouldAbort(p)
       \/ \E m \in received[p] : m.type = "DECISION" /\ m.content = "ABORT"
    /\ decision' = [decision EXCEPT ![p] = "ABORT"]
    /\ msgs' = msgs \cup {[type |-> "DECISION", from |-> p, content |-> "ABORT"]}
    /\ phase' = [phase EXCEPT ![p] = "DECIDED"]
    /\ UNCHANGED <<vote, crashed, suspected, received>>

\* Process p adopts a decision it received
AdoptDecision(p) ==
    /\ ~crashed[p]
    /\ decision[p] = "NONE"
    /\ \E m \in received[p] : 
        /\ m.type = "DECISION"
        /\ decision' = [decision EXCEPT ![p] = m.content]
        /\ phase' = [phase EXCEPT ![p] = "DECIDED"]
        /\ msgs' = msgs \cup {[type |-> "DECISION", from |-> p, content |-> m.content]}
    /\ UNCHANGED <<vote, crashed, suspected, received>>

\* Process p crashes
Crash(p) ==
    /\ ~crashed[p]
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, suspected, decision, msgs, received, phase>>

\* Failure detector suspects process p
Suspect(p) ==
    /\ Cardinality({q \in Proc : suspected[q]}) < MaxSuspected
    /\ ~suspected[p]
    /\ suspected' = [suspected EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, crashed, decision, msgs, received, phase>>

\* Process action - any action by a specific process
ProcessAction(p) ==
    \/ SendVote(p)
    \/ \E m \in msgs : ReceiveMessage(p, m)
    \/ DecideCommit(p)
    \/ DecideAbort(p)
    \/ AdoptDecision(p)

\* Environment action - crashes and suspicions
EnvironmentAction ==
    \/ \E p \in Proc : Crash(p)
    \/ \E p \in Proc : Suspect(p)

\* Next state relation
Next ==
    \/ \E p \in Proc : ProcessAction(p)
    \/ EnvironmentAction

\* Fairness conditions - weak fairness for non-stuttering process actions
Fairness ==
    /\ \A p \in Proc : WF_vars(SendVote(p))
    /\ \A p \in Proc : WF_vars(\E m \in msgs : ReceiveMessage(p, m))
    /\ \A p \in Proc : WF_vars(DecideCommit(p))
    /\ \A p \in Proc : WF_vars(DecideAbort(p))
    /\ \A p \in Proc : WF_vars(AdoptDecision(p))

\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* ====================