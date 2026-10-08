----------------------------- MODULE NBAC -----------------------------

EXTENDS TLC

CONSTANTS Proc, YES, NO, Vote0

ASSUME /\ YES # NO
       /\ Vote0 \in [Proc -> {YES, NO}]

\* Basic domains
Vals == {YES, NO}
Decisions == {"Undecided", "COMMIT", "ABORT"}
FDStates == {"ok", "crashed"}

Message == [from: Proc, to: Proc, val: Vals]

\* All possible protocol messages are determined by initial votes
AllMsgs == { [from |-> p, to |-> q, val |-> Vote0[p]] : p \in Proc, q \in Proc }

\* State variables
VARIABLES
  Crashed,      \* subset of Proc that have crashed (permanent)
  FD,           \* failure detector reports at each process
  Dec,          \* decision of each process
  Broadcasted,  \* set of processes that have broadcast their vote
  Sent,         \* set of messages that have been sent
  Rcvd          \* function Proc -> set of messages received by that proc

vars == <<Crashed, FD, Dec, Broadcasted, Sent, Rcvd>>

\* Helpers
MsgFromTo(p, q) == [from |-> p, to |-> q, val |-> Vote0[p]]
ReceivedFrom(p) == { m.from : m \in Rcvd[p] }
ReceivedAnyNO(p) == \E m \in Rcvd[p] : m.val = NO
ReceivedAllYes(p) ==
  /\ ReceivedFrom(p) = Proc
  /\ \A m \in Rcvd[p] : m.val = YES

\* Initial condition
Init ==
  /\ Crashed = {}
  /\ FD \in [Proc -> FDStates]
  /\ Dec = [p \in Proc |-> "Undecided"]
  /\ Broadcasted = {}
  /\ Sent = {}
  /\ Rcvd = [p \in Proc |-> {}]

\* Actions
Broadcast(p) ==
  /\ p \in Proc
  /\ p \notin Crashed
  /\ p \notin Broadcasted
  /\ Sent' = Sent \cup { MsgFromTo(p, q) : q \in Proc }
  /\ Broadcasted' = Broadcasted \cup {p}
  /\ UNCHANGED <<Crashed, FD, Dec, Rcvd>>

Deliver(q, m) ==
  /\ q \in Proc
  /\ m \in Sent
  /\ m.to = q
  /\ m \notin Rcvd[q]
  /\ Rcvd' = [Rcvd EXCEPT ![q] = @ \cup {m}]
  /\ UNCHANGED <<Crashed, FD, Dec, Broadcasted, Sent>>

Crash(p) ==
  /\ p \in Proc
  /\ p \notin Crashed
  /\ Crashed' = Crashed \cup {p}
  /\ UNCHANGED <<FD, Dec, Broadcasted, Sent, Rcvd>>

UpdateFD(p, s) ==
  /\ p \in Proc
  /\ s \in FDStates
  /\ FD' = [FD EXCEPT ![p] = s]
  /\ UNCHANGED <<Crashed, Dec, Broadcasted, Sent, Rcvd>>

DecideCommit(p) ==
  /\ p \in Proc
  /\ p \notin Crashed
  /\ Dec[p] = "Undecided"
  /\ ReceivedAllYes(p)
  /\ FD[p] = "ok"
  /\ Dec' = [Dec EXCEPT ![p] = "COMMIT"]
  /\ UNCHANGED <<Crashed, FD, Broadcasted, Sent, Rcvd>>

DecideAbort(p) ==
  /\ p \in Proc
  /\ p \notin Crashed
  /\ Dec[p] = "Undecided"
  /\ (ReceivedAnyNO(p) \/ FD[p] = "crashed")
  /\ Dec' = [Dec EXCEPT ![p] = "ABORT"]
  /\ UNCHANGED <<Crashed, FD, Broadcasted, Sent, Rcvd>>

Next ==
  \/ \E p \in Proc : Broadcast(p)
  \/ \E q \in Proc, m \in Sent : Deliver(q, m)
  \/ \E p \in Proc : Crash(p)
  \/ \E p \in Proc, s \in FDStates : UpdateFD(p, s)
  \/ \E p \in Proc : DecideCommit(p)
  \/ \E p \in Proc : DecideAbort(p)
  \/ UNCHANGED vars

\* Safety: type correctness and reliable asynchronous delivery discipline
TypeOK ==
  /\ Crashed \subseteq Proc
  /\ FD \in [Proc -> FDStates]
  /\ Dec \in [Proc -> Decisions]
  /\ Broadcasted \subseteq Proc
  /\ Sent \subseteq AllMsgs
  /\ Rcvd \in [Proc -> SUBSET AllMsgs]
  /\ \A p \in Proc : Rcvd[p] \subseteq { m \in Sent : m.to = p }

\* Validity: if any process commits then all initial votes were YES
Validity ==
  (\E p \in Proc : Dec[p] = "COMMIT") => (\A q \in Proc : Vote0[q] = YES)

\* Weak fairness: non-crashed processes that can broadcast or decide will eventually do so
Fairness ==
  /\ \A p \in Proc : WF_vars(Broadcast(p))
  /\ \A p \in Proc : WF_vars(DecideCommit(p))
  /\ \A p \in Proc : WF_vars(DecideAbort(p))

Spec == Init /\ [][Next]_vars /\ Fairness

THEOREM Spec => []TypeOK
THEOREM Spec => []Validity

======================================================================