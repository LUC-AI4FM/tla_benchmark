---------------------------- MODULE nbac ----------------------------
(***************************************************************************)
(* Non-Blocking Atomic Commitment (NBAC), after Raynal (1997).             *)
(* N processes, each with an initial vote YES or NO. Processes broadcast   *)
(* their vote, then decide COMMIT or ABORT based on the votes they have    *)
(* received and on a local, unreliable failure detector. Processes may     *)
(* crash permanently at any time. Message delivery is reliable but         *)
(* asynchronous: each received set grows monotonically within the set of   *)
(* sent messages.                                                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

Proc == 1 .. N

Votes == {"YES", "NO"}

PcValues == {"YES", "NO", "SENT", "COMMIT", "ABORT", "CRASH"}

Msgs == [src : Proc, type : Votes]

VARIABLES
    vote,   \* the initial vote of each process (never changes)
    pc,     \* control state of each process
    sent,   \* set of all messages ever broadcast
    rcvd,   \* rcvd[p] : messages received so far by p
    fd      \* fd[p] = TRUE iff p's failure detector reports a crash

vars == <<vote, pc, sent, rcvd, fd>>

---------------------------------------------------------------------------

TypeOK ==
    /\ vote \in [Proc -> Votes]
    /\ pc \in [Proc -> PcValues]
    /\ sent \subseteq Msgs
    /\ rcvd \in [Proc -> SUBSET Msgs]
    /\ \A p \in Proc : rcvd[p] \subseteq sent
    /\ fd \in [Proc -> BOOLEAN]

Init ==
    /\ vote \in [Proc -> Votes]
    /\ pc = vote
    /\ sent = {}
    /\ rcvd = [p \in Proc |-> {}]
    /\ fd = [p \in Proc |-> FALSE]

Alive(p) == pc[p] # "CRASH"

\* A process may crash at any time, permanently.
Crash(p) ==
    /\ Alive(p)
    /\ pc' = [pc EXCEPT ![p] = "CRASH"]
    /\ UNCHANGED <<vote, sent, rcvd, fd>>

\* Broadcast a YES vote.
SendYes(p) ==
    /\ pc[p] = "YES"
    /\ sent' = sent \cup {[src |-> p, type |-> "YES"]}
    /\ pc' = [pc EXCEPT ![p] = "SENT"]
    /\ UNCHANGED <<vote, rcvd, fd>>

\* Broadcast a NO vote.
SendNo(p) ==
    /\ pc[p] = "NO"
    /\ sent' = sent \cup {[src |-> p, type |-> "NO"]}
    /\ pc' = [pc EXCEPT ![p] = "SENT"]
    /\ UNCHANGED <<vote, rcvd, fd>>

\* Reliable, asynchronous delivery of one sent message.
Receive(p) ==
    /\ Alive(p)
    /\ \E m \in sent \ rcvd[p] :
          rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup {m}]
    /\ UNCHANGED <<vote, pc, sent, fd>>

\* The failure detector may change its output nondeterministically.
FailureDetector(p) ==
    /\ Alive(p)
    /\ fd' = [fd EXCEPT ![p] = ~ fd[p]]
    /\ UNCHANGED <<vote, pc, sent, rcvd>>

ReceivedNo(p) == \E m \in rcvd[p] : m.type = "NO"

ReceivedAllYes(p) ==
    \A q \in Proc : [src |-> q, type |-> "YES"] \in rcvd[p]

\* Abort on a suspected crash or any NO vote received.
DecideAbort(p) ==
    /\ pc[p] = "SENT"
    /\ fd[p] \/ ReceivedNo(p)
    /\ pc' = [pc EXCEPT ![p] = "ABORT"]
    /\ UNCHANGED <<vote, sent, rcvd, fd>>

\* Commit only with YES from everyone and no suspected crash.
DecideCommit(p) ==
    /\ pc[p] = "SENT"
    /\ ~ fd[p]
    /\ ~ ReceivedNo(p)
    /\ ReceivedAllYes(p)
    /\ pc' = [pc EXCEPT ![p] = "COMMIT"]
    /\ UNCHANGED <<vote, sent, rcvd, fd>>

Decide(p) == DecideAbort(p) \/ DecideCommit(p)

Next ==
    \E p \in Proc :
        \/ Crash(p)
        \/ SendYes(p)
        \/ SendNo(p)
        \/ Receive(p)
        \/ FailureDetector(p)
        \/ Decide(p)

Fairness ==
    \A p \in Proc :
        /\ WF_vars(SendYes(p))
        /\ WF_vars(SendNo(p))
        /\ WF_vars(Receive(p))
        /\ WF_vars(Decide(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------

\* Validity: if any process commits, then all processes initially voted YES.
Validity ==
    (\E p \in Proc : pc[p] = "COMMIT") => (\A q \in Proc : vote[q] = "YES")

\* Equivalent form: if any process voted NO, no process commits.
ValidityNo ==
    (\E q \in Proc : vote[q] = "NO") => (\A p \in Proc : pc[p] # "COMMIT")

=============================================================================