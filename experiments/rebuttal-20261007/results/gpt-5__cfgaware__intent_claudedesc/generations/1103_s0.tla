---- MODULE NBAC ----
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

(*
  Non-Blocking Atomic Commitment (NBAC), following Raynal (1997).
  Processes broadcast their initial vote (YES/NO), then decide COMMIT or ABORT.
  - Commit iff received YES from all processes and local failure detector says OK.
  - Abort if local failure detector suspects a crash, or if any NO is received.
  - Processes may crash permanently at any time.
  - Message delivery is reliable and asynchronous: each process's received set
    grows monotonically and is always a subset of the set of sent messages.
  - Weak fairness ensures that non-crashed processes that can broadcast or decide
    will eventually do so (if continuously enabled).
*)

Proc == 1..N
Vote == {"YES", "NO"}
DecVal == {"UNDECIDED", "COMMIT", "ABORT"}
Msg  == [from : Proc, vote : Vote]

VARIABLES
  votes,        \* initial votes per process (constant after Init)
  broadcasted,  \* set of processes that have broadcast their vote
  sent,         \* set of messages that have been sent
  recv,         \* function Proc -> set of messages received by that process
  decided,      \* function Proc -> decision in DecVal
  crashed,      \* set of crashed processes (monotonically increasing)
  FD            \* local failure detector reports per process: "OK" or "SUSPECT"

vars == << votes, broadcasted, sent, recv, decided, crashed, FD >>

MsgOf(p) == [from |-> p, vote |-> votes[p]]

Init ==
  /\ votes \in [Proc -> Vote]
  /\ broadcasted = {}
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]
  /\ decided = [p \in Proc |-> "UNDECIDED"]
  /\ crashed = {}
  /\ FD \in [Proc -> {"OK", "SUSPECT"}]

TypeOK ==
  /\ votes \in [Proc -> Vote]
  /\ broadcasted \subseteq Proc
  /\ sent = { MsgOf(p) : p \in broadcasted }
  /\ recv \in [Proc -> SUBSET sent]
  /\ decided \in [Proc -> DecVal]
  /\ crashed \subseteq Proc
  /\ FD \in [Proc -> {"OK", "SUSPECT"}]

AllYesReceived(p) ==
  \A q \in Proc: [from |-> q, vote |-> "YES"] \in recv[p]

AnyNOReceived(p) ==
  \E q \in Proc: [from |-> q, vote |-> "NO"] \in recv[p]

VoteBroadcast(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ p \notin broadcasted
  /\ broadcasted' = broadcasted \cup {p}
  /\ sent' = sent \cup {MsgOf(p)}
  /\ UNCHANGED << votes, recv, decided, crashed, FD >>

Deliver(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ \E m \in sent \ recv[p]:
       recv' = [recv EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED << votes, broadcasted, sent, decided, crashed, FD >>

DecideCommit(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ decided[p] = "UNDECIDED"
  /\ FD[p] = "OK"
  /\ AllYesReceived(p)
  /\ decided' = [decided EXCEPT ![p] = "COMMIT"]
  /\ UNCHANGED << votes, broadcasted, sent, recv, crashed, FD >>

DecideAbort(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ decided[p] = "UNDECIDED"
  /\ (FD[p] = "SUSPECT") \/ AnyNOReceived(p)
  /\ decided' = [decided EXCEPT ![p] = "ABORT"]
  /\ UNCHANGED << votes, broadcasted, sent, recv, crashed, FD >>

Decide(p) == DecideCommit(p) \/ DecideAbort(p)

Crash(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ crashed' = crashed \cup {p}
  /\ UNCHANGED << votes, broadcasted, sent, recv, decided, FD >>

FDChange(p) ==
  /\ p \in Proc
  /\ \E s \in {"OK", "SUSPECT"}:
       FD' = [FD EXCEPT ![p] = s]
  /\ UNCHANGED << votes, broadcasted, sent, recv, decided, crashed >>

Next ==
  \/ \E p \in Proc: VoteBroadcast(p)
  \/ \E p \in Proc: Deliver(p)
  \/ \E p \in Proc: Decide(p)
  \/ \E p \in Proc: Crash(p)
  \/ \E p \in Proc: FDChange(p)

Validity ==
  \A p \in Proc:
    decided[p] = "COMMIT" => (\A q \in Proc: votes[q] = "YES")

Fairness ==
  /\ \A p \in Proc: WF_vars(VoteBroadcast(p))
  /\ \A p \in Proc: WF_vars(Decide(p))

Spec == Init /\ [][Next]_vars /\ Fairness

====