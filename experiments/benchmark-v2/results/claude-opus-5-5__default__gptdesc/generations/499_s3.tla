```tla
vents
    /\ Cardinality(reqsMade) >= Cardinality(acksRecv)

THEOREM Spec => []TypeOK

---------------------------------------------------------------------------
(* Linearizability over observed client events *)

\* Position in observed of the request event for command c.
ReqPos(c) ==
    CHOOSE i \in 1..Len(observed) :
        observed[i].type = "Req" /\ observed[i].cmd = c

\* Position in observed of the acknowledgment event for command c.
AckPos(c) ==
    CHOOSE i \in 1..Len(observed) :
        observed[i].type = "Ack" /\ observed[i].cmd = c

\* Result returned to the client for command c.
ResultOf(c) == observed[AckPos(c)].val

\* Candidate total orders over all commands.
Orders == [1..NumCommands -> Commands]

IsPermutation(order) == Range(order) = Commands

\* Index of command c within the order.
OrderIdx(order, c) == CHOOSE j \in 1..NumCommands : order[j] = c

\* Result of the j-th command under sequential semantics.
ExpectedResult(order, j) ==
    IF order[j] \in Writes
      THEN order[j]
      ELSE LET ws == {k \in 1..(j - 1) : order[k] \in Writes}
           IN IF ws = {} THEN Nil ELSE order[MaxOf(ws)]

\* Write order constraints: a read returning write w must follow w.
WriteOrderOK(order) ==
    \A c \in Reads :
        ResultOf(c) # Nil =>
            OrderIdx(order, ResultOf(c)) < OrderIdx(order, c)

\* Sequential semantics: every observed result matches the order.
SequentialOK(order) ==
    \A j \in 1..NumCommands : ResultOf(order[j]) = ExpectedResult(order, j)

\* Real-time order: if c1 was acked before c2 was requested, c1 comes first.
RealTimeOK(order) ==
    \A c1, c2 \in Commands :
        AckPos(c1) < ReqPos(c2) => OrderIdx(order, c1) < OrderIdx(order, c2)

Linearizability ==
    terminated =>
        \E order \in Orders :
            /\ IsPermutation(order)
            /\ WriteOrderOK(order)
            /\ SequentialOK(order)
            /\ RealTimeOK(order)

THEOREM Spec => []Linearizability

=============================================================================
```

I need to correct one error in the earlier part of the output. The line of `=` characters right after `Spec == Init /\ [][Next]_vars` ends the module. SANY would then ignore every definition that follows it. That separator line must be replaced with a dash separator, like this:

```tla
Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* TLC-oriented model-checking helpers *)
```

The only `====` line in the module should be the final one shown above.