------------------------------- MODULE NBAC -------------------------------
(***************************************************************************)
(* Non-Blocking Atomic Commitment (NBAC), following Raynal (1997).         *)
(* N processes, each with an initial vote YES or NO, broadcast their vote  *)
(* and then decide COMMIT or ABORT based on received votes and a local     *)
(* (unreliable) failure detector. Processes may crash permanently.         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat \ {0}

Proc   == 1 .. N
Votes  == {"YES", "NO"}
Msgs   == [src : Proc, v : Votes]
States == {"INIT", "SENT", "COMMIT", "ABORT"}

VARIABLES
    vote,     \* initial vote of each process (fixed)
    pc,       \* local control state of each process
    crashed,  \* whether a process has crashed (permanent)
    sent,     \* set of all messages ever sent
    rcvd,     \* set of messages received by each process
    fd        \* failure detector output: TRUE = "some crash", FALSE = "all correct"

vars == <<vote, pc, crashed, sent, rcvd, fd>>

---------------------------------------------------------------------------
TypeOK ==
    /\ vote    \in [Proc -> Votes]
    /\ pc      \in [Proc -> States]
    /\ crashed \in [Proc -> BOOLEAN]
    /\ sent    \subseteq Msgs
    /\ rcvd    \in [Proc -> SUBSET Msgs]
    /\ \A p \in Proc : rcvd[p] \subseteq sent
    /\ fd      \in [Proc -> BOOLEAN]

Init ==
    /\ vote    \in [Proc -> Votes]
    /\ pc      = [p \in Proc |-> "INIT"]
    /\ crashed = [p \in Proc |-> FALSE]
    /\ sent    = {}
    /\ rcvd    = [p \in Proc |-> {}]
    /\ fd      \in [Proc -> BOOLEAN]

---------------------------------------------------------------------------
(* A process crashes permanently at any time. *)
Crash(p) ==
    /\ ~crashed[p]
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, pc, sent, rcvd, fd>>

(* A process broadcasts its initial vote. *)
SendVote(p) ==
    /\ ~crashed[p]
    /\ pc[p] = "INIT"
    /\ sent' = sent \cup {[src |-> p, v |-> vote[p]]}
    /\ pc'   = [pc EXCEPT ![p] = "SENT"]
    /\ UNCHANGED <<vote, crashed, rcvd, fd>>

(* Reliable, asynchronous delivery: received set grows monotonically    *)
(* as a subset of the sent messages.                                    *)
Receive(p) ==
    /\ ~crashed[p]
    /\ \E m \in sent \ rcvd[p] :
          rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup {m}]
    /\ UNCHANGED <<vote, pc, crashed, sent, fd>>

(* The failure detector may nondeterministically change its output. *)
FailureDetector(p) ==
    /\ ~crashed[p]
    /\ \E b \in BOOLEAN : fd' = [fd EXCEPT ![p] = b]
    /\ UNCHANGED <<vote, pc, crashed, sent, rcvd>>

AllYesReceived(p) ==
    \A q \in Proc : [src |-> q, v |-> "YES"] \in rcvd[p]

SomeNoReceived(p) ==
    \E m \in rcvd[p] : m.v = "NO"

(* Commit only if YES received from all and FD reports no crash. *)
Commit(p) ==
    /\ ~crashed[p]
    /\ pc[p] = "SENT"
    /\ AllYesReceived(p)
    /\ fd[p] = FALSE
    /\ pc' = [pc EXCEPT ![p] = "COMMIT"]
    /\ UNCHANGED <<vote, crashed, sent, rcvd, fd>>

(* Abort if a crash is suspected or a NO vote is received. *)
Abort(p) ==
    /\ ~crashed[p]
    /\ pc[p] = "SENT"
    /\ fd[p] = TRUE \/ SomeNoReceived(p)
    /\ pc' = [pc EXCEPT ![p] = "ABORT"]
    /\ UNCHANGED <<vote, crashed, sent, rcvd, fd>>

Decide(p) == Commit(p) \/ Abort(p)

Next ==
    \E p \in Proc :
        \/ Crash(p)
        \/ SendVote(p)
        \/ Receive(p)
        \/ FailureDetector(p)
        \/ Decide(p)

Fairness ==
    \A p \in Proc :
        /\ WF_vars(SendVote(p))
        /\ WF_vars(Receive(p))
        /\ WF_vars(Decide(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Validity: if any process commits, then all processes voted YES. *)
Validity ==
    (\E p \in Proc : pc[p] = "COMMIT") => (\A q \in Proc : vote[q] = "YES")

(* Equivalent formulation: if any process voted NO, nobody commits. *)
ValidityNo ==
    (\E q \in Proc : vote[q] = "NO") => (\A p \in Proc : pc[p] # "COMMIT")

THEOREM Spec => [](TypeOK /\ Validity /\ ValidityNo)
=============================================================================