---------------------------- MODULE RingLeaderElection ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, Id

NVal == 4
IdVal == <<2, 4, 1, 3>>

Nodes == 1..N

ASSUME N \in Nat \ {0}
ASSUME Id \in [Nodes -> Nat \ {0}]
ASSUME \A i, j \in Nodes : i # j => Id[i] # Id[j]

succ(n) == IF n = N THEN 1 ELSE n + 1

IdSet == {Id[n] : n \in Nodes}
MaxId == CHOOSE x \in IdSet : \A y \in IdSet : y <= x

States == {"idle", "part", "lost", "won", "done"}
Msgs   == [type : {"elect", "leader"}, id : IdSet]

VARIABLES msgs, state, leader, initiated

vars == <<msgs, state, leader, initiated>>

-----------------------------------------------------------------------------
Send(q, n, m) == [q EXCEPT ![succ(n)] = Append(q[succ(n)], m)]
Pop(n)        == [msgs EXCEPT ![n] = Tail(msgs[n])]
PopSend(n, m) == Send(Pop(n), n, m)

Init ==
  /\ msgs      = [n \in Nodes |-> <<>>]
  /\ state     = [n \in Nodes |-> "idle"]
  /\ leader    = [n \in Nodes |-> 0]
  /\ initiated = [n \in Nodes |-> FALSE]

Initiate(n) ==
  /\ state[n] = "idle"
  /\ state'     = [state EXCEPT ![n] = "part"]
  /\ initiated' = [initiated EXCEPT ![n] = TRUE]
  /\ msgs'      = Send(msgs, n, [type |-> "elect", id |-> Id[n]])
  /\ UNCHANGED leader

ReceiveElect(n) ==
  /\ msgs[n] # <<>>
  /\ Head(msgs[n]).type = "elect"
  /\ LET m == Head(msgs[n]) IN
       CASE m.id > Id[n] /\ state[n] \in {"idle", "part", "lost"} ->
              /\ msgs'  = PopSend(n, m)
              /\ state' = [state EXCEPT ![n] = "lost"]
              /\ UNCHANGED <<leader, initiated>>
         [] m.id < Id[n] /\ state[n] = "idle" ->
              /\ msgs'  = PopSend(n, [type |-> "elect", id |-> Id[n]])
              /\ state' = [state EXCEPT ![n] = "part"]
              /\ UNCHANGED <<leader, initiated>>
         [] m.id = Id[n] ->
              /\ msgs'   = PopSend(n, [type |-> "leader", id |-> Id[n]])
              /\ state'  = [state EXCEPT ![n] = "won"]
              /\ leader' = [leader EXCEPT ![n] = Id[n]]
              /\ UNCHANGED initiated
         [] OTHER ->
              /\ msgs' = Pop(n)
              /\ UNCHANGED <<state, leader, initiated>>

ReceiveLeader(n) ==
  /\ msgs[n] # <<>>
  /\ Head(msgs[n]).type = "leader"
  /\ LET m == Head(msgs[n]) IN
       IF m.id = Id[n]
         THEN /\ msgs'  = Pop(n)
              /\ state' = [state EXCEPT ![n] = "done"]
              /\ UNCHANGED <<leader, initiated>>
         ELSE /\ msgs'   = PopSend(n, m)
              /\ state'  = [state EXCEPT ![n] = "done"]
              /\ leader' = [leader EXCEPT ![n] = m.id]
              /\ UNCHANGED initiated

Receive(n) == ReceiveElect(n) \/ ReceiveLeader(n)

Terminated ==
  /\ \A n \in Nodes : state[n] = "done" /\ msgs[n] = <<>>

Done == Terminated /\ UNCHANGED vars

Next ==
  \/ \E n \in Nodes : Initiate(n) \/ Receive(n)
  \/ Done

Fairness ==
  /\ \A n \in Nodes : WF_vars(Receive(n))
  /\ WF_vars(\E n \in Nodes : Initiate(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
TypeOK ==
  /\ msgs      \in [Nodes -> Seq(Msgs)]
  /\ state     \in [Nodes -> States]
  /\ leader    \in [Nodes -> {0} \cup IdSet]
  /\ initiated \in [Nodes -> BOOLEAN]

IsLeader(n) == state[n] \in {"won", "done"} /\ leader[n] = Id[n]

\* Message integrity: identifiers carried are always genuine process ids,
\* and leader announcements only ever carry the maximum id.
MessageIntegrity ==
  \A n \in Nodes : \A k \in 1..Len(msgs[n]) :
     /\ msgs[n][k].id \in IdSet
     /\ msgs[n][k].type = "leader" => msgs[n][k].id = MaxId

AgreementOK ==
  \A i, j \in Nodes : (leader[i] # 0 /\ leader[j] # 0) => leader[i] = leader[j]

MaxLeaderOK ==
  \A i \in Nodes : leader[i] # 0 => leader[i] = MaxId

UniqueLeaderOK ==
  \A i, j \in Nodes : IsLeader(i) /\ IsLeader(j) => i = j

TerminationOK ==
  Terminated => \A n \in Nodes : leader[n] = MaxId

Correctness ==
  /\ AgreementOK
  /\ MaxLeaderOK
  /\ UniqueLeaderOK
  /\ MessageIntegrity
  /\ TerminationOK

\* Liveness: eventually a leader is elected and known to all processes.
EventuallyElected == <>(\A n \in Nodes : leader[n] = MaxId)
EventuallyTerminated == <>Terminated

THEOREM Spec => [](TypeOK /\ Correctness)
THEOREM Spec => EventuallyElected /\ EventuallyTerminated
=============================================================================