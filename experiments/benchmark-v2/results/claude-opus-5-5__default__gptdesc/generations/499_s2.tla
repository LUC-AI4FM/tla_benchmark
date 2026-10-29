```tla
 Len(pending) <= NumCommands
  /\ observed \in Seq(ClientEvents)
  /\ Len(observed) <= 2 * NumCommands
  /\ NumReqs <= NumCommands
  /\ NumAcks <= NumReqs
  /\ Len(pending) + NumReqs = NumCommands

----------------------------------------------------------------------------
(* Linearizability over observed client events *)

ReqPosOfCmd(c) ==
  CHOOSE i \in DOMAIN observed :
    observed[i].type = "Req" /\ observed[i].cmd = c

AckPosOfCmd(c) ==
  CHOOSE i \in DOMAIN observed :
    observed[i].type = "Ack" /\ observed[i].cmd = c

ResultOfCmd(c) == observed[AckPosOfCmd(c)].val

OrderIdxOfCmd(order, c) == CHOOSE j \in 1..NumCommands : order[j] = c

LastWriteBefore(order, j) ==
  LET ws == {k \in 1..NumCommands : k < j /\ order[k] \in Writes}
  IN IF ws = {} THEN "nil" ELSE order[Max(ws)]

\* Every read returns the value of the latest preceding write in the order.
SequentialOK(order) ==
  \A j \in 1..NumCommands :
    order[j] \in Reads => ResultOfCmd(order[j]) = LastWriteBefore(order, j)

\* If c1 was acknowledged before c2 was requested, c1 precedes c2.
RealTimeOK(order) ==
  \A c1, c2 \in Commands :
    AckPosOfCmd(c1) < ReqPosOfCmd(c2) =>
      OrderIdxOfCmd(order, c1) < OrderIdxOfCmd(order, c2)

Linearizability ==
  terminated =>
    \E order \in CmdPerms : SequentialOK(order) /\ RealTimeOK(order)

----------------------------------------------------------------------------
(* Top-level correctness theorems *)

THEOREM Spec => []TypeOK
THEOREM Spec => []Linearizability

=============================================================================
```