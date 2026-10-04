--------------------------- MODULE NonBlockingAtomicCommitment ---------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
    Proc,           \* Set of processes
    AllYes,         \* Boolean: if TRUE, all processes initially vote YES
    AllNo           \* Boolean: if TRUE, all processes initially vote NO

VARIABLES
    vote,           \* vote[p] = "YES" or "NO" - initial vote of process p
    crashed,        \* crashed[p] = TRUE iff process p has crashed
    suspected,      \* suspected[p] = TRUE iff process p is suspected by failure detector
    decision,       \* decision[p] = "COMMIT", "ABORT", or "NONE" (no decision yet)
    mailbox,        \* mailbox[p] = set of messages received by process p
    sent            \* sent = set of all messages that have been sent

\* Message types
\* {"VOTE", sender, vote_value}
\* {"DECISION", sender, decision_value}

TypeOK ==
    /\ vote \in [Proc -> {"YES", "NO"}]
    /\ crashed \in [Proc -> BOOLEAN]
    /\ suspected \in [Proc -> BOOLEAN]
    /\ decision \in [Proc -> {"COMMIT", "ABORT", "NONE"}]
    /\ mailbox \in [Proc -> SUBSET (Proc \times {"YES", "NO", "COMMIT", "ABORT"})]
    /\ sent \in SUBSET (Proc \times {"YES", "NO", "COMMIT", "ABORT"})

\* Initial state
Init ==
    /\ vote = [p \in Proc |-> IF AllYes THEN "YES" ELSE IF AllNo THEN "NO" ELSE "YES"]
    /\ crashed = [p \in Proc |-> FALSE]
    /\ suspected = [p \in Proc |-> FALSE]
    /\ decision = [p \in Proc |-> "NONE"]
    /\ mailbox = [p \in Proc |-> {}]
    /\ sent = {}

\* Process p sends its vote to all other processes
SendVote(p) ==
    /\ ~crashed[p]
    /\ <<p, vote[p]>> \notin sent
    /\ sent' = sent \cup {<<p, vote[p]>>}
    /\ UNCHANGED <<vote, crashed, suspected, decision, mailbox>>

\* Process p receives a message m from sent messages
ReceiveMessage(p) ==
    /\ ~crashed[p]
    /\ \E m \in sent : m \notin mailbox[p]
    /\ \E m \in sent :
        /\ m \notin mailbox[p]
        /\ mailbox' = [mailbox EXCEPT ![p] = @ \cup {m}]
    /\ UNCHANGED <<vote, crashed, suspected, decision, sent>>

\* Check if process p has received YES votes from all processes
ReceivedAllYes(p) ==
    \A q \in Proc : <<q, "YES">> \in mailbox[p]

\* Check if process p has received any NO vote
ReceivedAnyNo(p) ==
    \E q \in Proc : <<q, "NO">> \in mailbox[p]

\* Check if process p has received an ABORT decision
ReceivedAbort(p) ==
    \E q \in Proc : <<q, "ABORT">> \in mailbox[p]

\* Check if process p has received a COMMIT decision
ReceivedCommit(p) ==
    \E q \in Proc : <<q, "COMMIT">> \in mailbox[p]

\* Check if any process is suspected
AnySuspected(p) ==
    \E q \in Proc : suspected[q]

\* Process p decides to COMMIT
DecideCommit(p) ==
    /\ ~crashed[p]
    /\ decision[p] = "NONE"
    /\ ReceivedAllYes(p)
    /\ ~AnySuspected(p)
    /\ ~ReceivedAbort(p)
    /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
    /\ sent' = sent \cup {<<p, "COMMIT">>}
    /\ UNCHANGED <<vote, crashed, suspected, mailbox>>

\* Process p decides to ABORT due to NO vote or suspicion
DecideAbort(p) ==
    /\ ~crashed[p]
    /\ decision[p] = "NONE"
    /\ \/ ReceivedAnyNo(p)
       \/ AnySuspected(p)
       \/ ReceivedAbort(p)
       \/ vote[p] = "NO"
    /\ decision' = [decision EXCEPT ![p] = "ABORT"]
    /\ sent' = sent \cup {<<p, "ABORT">>}
    /\ UNCHANGED <<vote, crashed, suspected, mailbox>>

\* Process p adopts COMMIT decision from another process
AdoptCommit(p) ==
    /\ ~crashed[p]
    /\ decision[p] = "NONE"
    /\ ReceivedCommit(p)
    /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
    /\ sent' = sent \cup {<<p, "COMMIT">>}
    /\ UNCHANGED <<vote, crashed, suspected, mailbox>>

\* Process p adopts ABORT decision from another process
AdoptAbort(p) ==
    /\ ~crashed[p]
    /\ decision[p] = "NONE"
    /\ ReceivedAbort(p)
    /\ decision' = [decision EXCEPT ![p] = "ABORT"]
    /\ sent' = sent \cup {<<p, "ABORT">>}
    /\ UNCHANGED <<vote, crashed, suspected, mailbox>>

\* Process p crashes
Crash(p) ==
    /\ ~crashed[p]
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, suspected, decision, mailbox, sent>>

\* Failure detector suspects process p
Suspect(p) ==
    /\ ~suspected[p]
    /\ suspected' = [suspected EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, crashed, decision, mailbox, sent>>

\* Failure detector stops suspecting process p (for unreliable FD)
Unsuspect(p) ==
    /\ suspected[p]
    /\ suspected' = [suspected EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<vote, crashed, decision, mailbox, sent>>

\* Process action for process p
ProcessAction(p) ==
    \/ SendVote(p)
    \/ ReceiveMessage(p)
    \/ DecideCommit(p)
    \/ DecideAbort(p)
    \/ AdoptCommit(p)
    \/ AdoptAbort(p)

\* Environment action (crashes and failure detector)
EnvironmentAction ==
    \E p \in Proc :
        \/ Crash(p)
        \/ Suspect(p)
        \/ Unsuspect(p)

\* Next state relation
Next ==
    \/ \E p \in Proc : ProcessAction(p)
    \/ EnvironmentAction

\* Stuttering step for a process (either does something or stutters)
ProcessEnabled(p) ==
    \/ (~crashed[p] /\ <<p, vote[p]>> \notin sent)
    \/ (~crashed[p] /\ \E m \in sent : m \notin mailbox[p])
    \/ (~crashed[p] /\ decision[p] = "NONE" /\ ReceivedAllYes(p) /\ ~AnySuspected(p) /\ ~ReceivedAbort(p))
    \/ (~crashed[p] /\ decision[p] = "NONE" /\ (ReceivedAnyNo(p) \/ AnySuspected(p) \/ ReceivedAbort(p) \/ vote[p] = "NO"))
    \/ (~crashed[p] /\ decision[p] = "NONE" /\ ReceivedCommit(p))
    \/ (~crashed[p] /\ decision[p] = "NONE" /\ ReceivedAbort(p))

\* Fairness: Weak fairness for process actions
Fairness ==
    \A p \in Proc : WF_<<vote, crashed, suspected, decision, mailbox, sent>>(ProcessAction(p))

\* Specification with fairness
Spec == Init /\ [][Next]_<<vote, crashed, suspected, decision, mailbox, sent>> /\ Fairness

\* ============================================================================