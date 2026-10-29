```tla
       Cardinality(reqsMade) >= Cardinality(acksRecv)

THEOREM TypeCorrectness == Spec => []TypeOK

----------------------------------------------------------------------------
(*******************************)
(* Linearizability constraint. *)
(*******************************)
ReqPosOfCmd(c) == CHOOSE i \in 1..Len(observed) :
                     /\ observed[i].type = "Req"
                     /\ observed[i].cmd = c

AckPosOfCmd(c) == CHOOSE i \in 1..Len(observed) :
                     /\ observed[i].type = "Ack"
                     /\ observed[i].cmd = c

ResultOfCmd(c) == observed[AckPosOfCmd(c)].val

OrderIdxOfCmd(order, c) == CHOOSE j \in 1..NumCommands : order[j] = c

LastWriteBefore(order, j) ==
    LET ws == {k \in 1..(j - 1) : order[k] \in Writes}
    IN  IF ws = {} THEN NilCmd ELSE order[MaxOf(ws)]

IsLinearOrder(order) ==
    /\ {order[j] : j \in 1..NumCommands} = Commands
    /\ \A j \in 1..NumCommands :
          ResultOfCmd(order[j]) = LastWriteBefore(order, j)

ObeysRealTime(order) ==
    \A c1, c2 \in Commands :
        (AckPosOfCmd(c1) < ReqPosOfCmd(c2))
            => (OrderIdxOfCmd(order, c1) < OrderIdxOfCmd(order, c2))

Linearizability ==
    terminated =>
        \E order \in [1..NumCommands -> Commands] :
            /\ IsLinearOrder(order)
            /\ ObeysRealTime(order)

THEOREM LinearizabilityCorrectness == Spec => []Linearizability

=============================================================================
```