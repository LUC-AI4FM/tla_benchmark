---------------------------- MODULE NBAC ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

Vote == {"YES", "NO"}
Decision == {"COMMIT", "ABORT"}
FDReport == {"CRASHED", "ALL_CORRECT"}

VARIABLES
    initialVote,    \* initialVote[p] \in Vote: the initial vote of process p
    voted,          \* voted[p] \in BOOLEAN: whether process p has broadcast its vote
    crashed,        \* crashed[p] \in BOOLEAN: whether process p has crashed
    sent,           \* sent: set of <<sender, vote>> pairs that have been broadcast
    received,       \* received[p]: set of <<sender, vote>> pairs received by process p
    fdReport,       \* fdReport[p] \in FDReport: current failure detector report at process p
    decision        \* decision[p] \in Decision \cup {"NONE"}: decision made by process p

vars == <<initialVote, voted, crashed, sent, received, fdReport, decision>>

TypeOK ==
    /\ initialVote \in [Procs -> Vote]
    /\ voted \in [Procs -> BOOLEAN]
    /\ crashed \in [Procs -> BOOLEAN]
    /\ sent \subseteq (Procs \X Vote)
    /\ received \in [Procs -> SUBSET (Procs \X Vote)]
    /\ fdReport \in [Procs -> FDReport]
    /\ decision \in [Procs -> Decision \cup {"NONE"}]

Init ==
    /\ initialVote \in [Procs -> Vote]
    /\ voted = [p \in Procs |-> FALSE]
    /\ crashed = [p \in Procs |-> FALSE]
    /\ sent = {}
    /\ received = [p \in Procs |-> {}]
    /\ fdReport \in [Procs -> FDReport]
    /\ decision = [p \in Procs |-> "NONE"]

\* Process p broadcasts its vote
Broadcast(p) ==
    /\ ~crashed[p]
    /\ ~voted[p]
    /\ voted' = [voted EXCEPT ![p] = TRUE]
    /\ sent' = sent \cup {<<p, initialVote[p]>>}
    /\ UNCHANGED <<initialVote, crashed, received, fdReport, decision>>

\* Process p receives some new messages from sent
Receive(p) ==
    /\ ~crashed[p]
    /\ \E msgs \in SUBSET sent :
        /\ msgs \ received[p] # {}  \* receive at least one new message
        /\ received' = [received EXCEPT ![p] = received[p] \cup msgs]
    /\ UNCHANGED <<initialVote, voted, crashed, sent, fdReport, decision>>

\* Failure detector at process p updates its report
UpdateFD(p) ==
    /\ ~crashed[p]
    /\ fdReport' = [fdReport EXCEPT ![p] \in FDReport]
    /\ UNCHANGED <<initialVote, voted, crashed, sent, received, decision>>

\* Process p decides to COMMIT
DecideCommit(p) ==
    /\ ~crashed[p]
    /\ decision[p] = "NONE"
    /\ voted[p]
    \* Received YES from all processes
    /\ \A q \in Procs : <<q, "YES">> \in received[p]
    \* Failure detector reports no crashes
    /\ fdReport[p] = "ALL_CORRECT"
    /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
    /\ UNCHANGED <<initialVote, voted, crashed, sent, received, fdReport>>

\* Process p decides to ABORT
DecideAbort(p) ==
    /\ ~crashed[p]
    /\ decision[p] = "NONE"
    /\ voted[p]
    \* Either received a NO vote or failure detector reports a crash
    /\ \/ \E q \in Procs : <<q, "NO">> \in received[p]
       \/ fdReport[p] = "CRASHED"
    /\ decision' = [decision EXCEPT ![p] = "ABORT"]
    /\ UNCHANGED <<initialVote, voted, crashed, sent, received, fdReport>>

\* Process p crashes
Crash(p) ==
    /\ ~crashed[p]
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<initialVote, voted, sent, received, fdReport, decision>>

Next ==
    \E p \in Procs :
        \/ Broadcast(p)
        \/ Receive(p)
        \/ UpdateFD(p)
        \/ DecideCommit(p)
        \/ DecideAbort(p)
        \/ Crash(p)

\* Fairness: non-crashed processes that can vote or decide will eventually do so
Fairness ==
    /\ \A p \in Procs : WF_vars(Broadcast(p))
    /\ \A p \in Procs : WF_vars(DecideCommit(p))
    /\ \A p \in Procs : WF_vars(DecideAbort(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Validity: If any process commits, then all processes voted YES
\* Equivalently: If any process voted NO, no process may commit
Validity ==
    \A p \in Procs :
        decision[p] = "COMMIT" => \A q \in Procs : initialVote[q] = "YES"

=============================================================================