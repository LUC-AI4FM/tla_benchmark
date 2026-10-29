---------------------------- MODULE ConcurrentRegister ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Clients,    \* set of clients (a model parameter; may be any set)
    Addrs,      \* finite set of register addresses
    Vals,       \* set of values that writes may store
    InitVal,    \* initial value of every register
    MaxOps      \* bound on the number of issued operations (for model checking)

ASSUME MaxOps \in Nat
ASSUME IsFiniteSet(Addrs)

InitSrc == 0          \* special "initial write" source
NoOp    == 0          \* marks a free per-client per-register slot

VARIABLES
    ops,     \* sequence of issued operations; index = operation id
    slot,    \* slot[c][a] = id of c's outstanding op on a, or NoOp
    cq,      \* cq[c] = per-client FIFO queue of outstanding op ids
    po       \* recorded partial order: set of pairs <<i, j>> (i before j)

vars == <<ops, slot, cq, po>>

Ids == 1..MaxOps

OpRec == [client : Clients,
          type   : {"R", "W"},
          addr   : Addrs,
          val    : Vals \cup {InitVal},
          src    : {InitSrc} \cup Ids,
          status : {"pending", "done"}]

IssuedIds == DOMAIN ops

WritesTo(o, a) == {k \in DOMAIN o : o[k].type = "W" /\ o[k].addr = a}

-----------------------------------------------------------------------------
(* Serializability: existence of a total order (position function) that      *)
(* extends the partial order, respects program order, and makes every         *)
(* completed read observe its recorded source as the latest preceding write.  *)
-----------------------------------------------------------------------------

IsBijection(pos, D) ==
    \A i, j \in D : i # j => pos[i] # pos[j]

ReadOK(o, pos, r) ==
    LET a == o[r].addr
        w == o[r].src
    IN  IF w = InitSrc
          THEN \A k \in WritesTo(o, a) : pos[r] < pos[k]
          ELSE /\ pos[w] < pos[r]
               /\ \A k \in WritesTo(o, a) \ {w} :
                     ~(pos[w] < pos[k] /\ pos[k] < pos[r])

SerialOrderOK(o, rel, pos) ==
    /\ \A p \in rel : pos[p[1]] < pos[p[2]]
    /\ \A i, j \in DOMAIN o :
          (o[i].client = o[j].client /\ i < j) => pos[i] < pos[j]
    /\ \A r \in DOMAIN o :
          (o[r].type = "R" /\ o[r].status = "done") => ReadOK(o, pos, r)

Serializable(o, rel) ==
    \E pos \in [DOMAIN o -> 1..Len(o)] :
        /\ IsBijection(pos, DOMAIN o)
        /\ SerialOrderOK(o, rel, pos)

-----------------------------------------------------------------------------

Init ==
    /\ ops  = << >>
    /\ slot = [c \in Clients |-> [a \in Addrs |-> NoOp]]
    /\ cq   = [c \in Clients |-> << >>]
    /\ po   = {}

\* Edges added when issuing a new op: program order (all earlier ops of the
\* same client) and real-time order (all already-completed ops).
IssueEdges(c, id) ==
    { <<k, id>> : k \in { j \in IssuedIds :
                            ops[j].client = c \/ ops[j].status = "done" } }

Issue(c, a, t, v) ==
    /\ Len(ops) < MaxOps
    /\ slot[c][a] = NoOp
    /\ LET id  == Len(ops) + 1
           rec == [client |-> c, type |-> t, addr |-> a, val |-> v,
                   src |-> InitSrc, status |-> "pending"]
       IN  /\ ops'  = Append(ops, rec)
           /\ slot' = [slot EXCEPT ![c][a] = id]
           /\ cq'   = [cq EXCEPT ![c] = Append(@, id)]
           /\ po'   = po \cup IssueEdges(c, id)

IssueRead(c, a)     == Issue(c, a, "R", InitVal)
IssueWrite(c, a, v) == Issue(c, a, "W", v)

CompleteWrite(c) ==
    /\ cq[c] # << >>
    /\ LET id == Head(cq[c])
       IN  /\ ops[id].type = "W"
           /\ ops'  = [ops EXCEPT ![id].status = "done"]
           /\ slot' = [slot EXCEPT ![c][ops[id].addr] = NoOp]
           /\ cq'   = [cq EXCEPT ![c] = Tail(@)]
           /\ UNCHANGED po

ReadEdges(r, w, a) ==
    IF w = InitSrc
      THEN { <<r, k>> : k \in WritesTo(ops, a) }
      ELSE { <<w, r>> }

CompleteRead(c, w) ==
    /\ cq[c] # << >>
    /\ LET r  == Head(cq[c])
           a  == ops[r].addr
       IN  /\ ops[r].type = "R"
           /\ w \in {InitSrc} \cup WritesTo(ops, a)
           /\ LET newOps == [ops EXCEPT
                               ![r].src    = w,
                               ![r].val    = IF w = InitSrc THEN InitVal
                                                            ELSE ops[w].val,
                               ![r].status = "done"]
                  newPo  == po \cup ReadEdges(r, w, a)
              IN  /\ Serializable(newOps, newPo)
                  /\ ops' = newOps
                  /\ po'  = newPo
           /\ slot' = [slot EXCEPT ![c][a] = NoOp]
           /\ cq'   = [cq EXCEPT ![c] = Tail(@)]

Next ==
    \/ \E c \in Clients, a \in Addrs : IssueRead(c, a)
    \/ \E c \in Clients, a \in Addrs, v \in Vals : IssueWrite(c, a, v)
    \/ \E c \in Clients : CompleteWrite(c)
    \/ \E c \in Clients : \E w \in {InitSrc} \cup Ids : CompleteRead(c, w)

Fairness ==
    \A c \in Clients :
        /\ WF_vars(CompleteWrite(c))
        /\ WF_vars(\E w \in {InitSrc} \cup Ids : CompleteRead(c, w))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Invariants                                                                 *)
-----------------------------------------------------------------------------

TypeOK ==
    /\ ops \in Seq(OpRec)
    /\ Len(ops) <= MaxOps
    /\ slot \in [Clients -> [Addrs -> {NoOp} \cup Ids]]
    /\ cq \in [Clients -> Seq(Ids)]
    /\ po \subseteq (IssuedIds \X IssuedIds)

\* Per-client queue structure, slot occupancy, and metadata consistency
QueueInv ==
    /\ \A c \in Clients :
         /\ \A i \in 1..Len(cq[c]) :
              /\ cq[c][i] \in IssuedIds
              /\ ops[cq[c][i]].client = c
              /\ ops[cq[c][i]].status = "pending"
         /\ \A i, j \in 1..Len(cq[c]) : i < j => cq[c][i] < cq[c][j]
    /\ \A k \in IssuedIds :
         ops[k].status = "pending" =>
            \E i \in 1..Len(cq[ops[k].client]) : cq[ops[k].client][i] = k

SlotInv ==
    \A c \in Clients, a \in Addrs :
        /\ slot[c][a] # NoOp =>
              /\ slot[c][a] \in IssuedIds
              /\ ops[slot[c][a]].client = c
              /\ ops[slot[c][a]].addr = a
              /\ ops[slot[c][a]].status = "pending"
        /\ \A k \in IssuedIds :
              (ops[k].client = c /\ ops[k].addr = a /\ ops[k].status = "pending")
                 => slot[c][a] = k

\* Every completed read returns the initial value or the value of some write
\* to the same address, matching its recorded source.
ReadValueInv ==
    \A r \in IssuedIds :
        (ops[r].type = "R" /\ ops[r].status = "done") =>
            IF ops[r].src = InitSrc
              THEN ops[r].val = InitVal
              ELSE /\ ops[r].src \in IssuedIds
                     /\ ops[ops[r].src].type = "W"
                     /\ ops[ops[r].src].addr = ops[r].addr
                     /\ ops[r].val = ops[ops[r].src].val

\* Global sequential ordering consistent with po, program order, and sources
SerializabilityInv == Serializable(ops, po)

Safety ==
    /\ TypeOK
    /\ QueueInv
    /\ SlotInv
    /\ ReadValueInv
    /\ SerializabilityInv

-----------------------------------------------------------------------------
(* Liveness                                                                   *)
-----------------------------------------------------------------------------

PendingOp(i) == i \in DOMAIN ops /\ ops[i].status = "pending"
DoneOp(i)    == i \in DOMAIN ops /\ ops[i].status = "done"

EventualCompletion ==
    \A i \in Ids : [](PendingOp(i) => <>DoneOp(i))

THEOREM Spec => []Safety
THEOREM Spec => EventualCompletion
=============================================================================