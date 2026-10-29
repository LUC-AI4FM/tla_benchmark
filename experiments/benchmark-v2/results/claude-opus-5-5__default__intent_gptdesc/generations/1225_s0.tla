------------------------------ MODULE RequestOrdering ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Proc,       \* finite set of processors
    Adr,        \* finite set of memory addresses (registers)
    Val,        \* finite set of data values
    NoVal,      \* placeholder value carried by read requests
    MaxQLen     \* bound on each per-processor queue length

ASSUME ConstAssumptions ==
    /\ Proc # {}
    /\ Adr # {}
    /\ NoVal \notin Val
    /\ MaxQLen \in Nat \ {0}

VARIABLES
    queue,      \* queue[p] : sequence of requests issued by processor p
    order       \* set of pairs <<id1, id2>>: request id1 is ordered before id2

vars == <<queue, order>>

-----------------------------------------------------------------------------
(* Requests and request identifiers                                        *)
-----------------------------------------------------------------------------

Request ==
         [op : {"Rd"}, adr : Adr, val : {NoVal}]
    \cup [op : {"Wr"}, adr : Adr, val : Val]

\* A request is identified by its issuing processor and its position in that
\* processor's queue.
IdUniverse == Proc \X (1..MaxQLen)

\* Identifiers of all requests that currently exist.
ExistingIds == UNION { { <<p, i>> : i \in 1..Len(queue[p]) } : p \in Proc }

\* Identifiers of requests already issued by processor p.
ProcIds(p) == { <<p, i>> : i \in 1..Len(queue[p]) }

\* Elements ordered before some element of S (S is closed downward by this).
DownClosure(S) == S \cup { x \in ExistingIds : \E y \in S : <<x, y>> \in order }

-----------------------------------------------------------------------------
(* Type invariant                                                          *)
-----------------------------------------------------------------------------

TypeOK ==
    /\ queue \in [Proc -> Seq(Request)]
    /\ \A p \in Proc : Len(queue[p]) <= MaxQLen
    /\ order \subseteq (IdUniverse \X IdUniverse)
    /\ \A r \in order : r[1] \in ExistingIds /\ r[2] \in ExistingIds

-----------------------------------------------------------------------------
(* Initial state                                                           *)
-----------------------------------------------------------------------------

Init ==
    /\ queue = [p \in Proc |-> << >>]
    /\ order = {}

-----------------------------------------------------------------------------
(* Transitions                                                             *)
-----------------------------------------------------------------------------

(* Processor p issues request req.  The new request is appended to p's     *)
(* queue and placed after all earlier requests of p, plus a                *)
(* nondeterministically chosen set S of other existing requests.  To keep  *)
(* the order transitive, the new request is placed after everything that   *)
(* precedes any of its chosen predecessors.  Because the new request is    *)
(* maximal, the extended relation stays a strict partial order.            *)
Issue(p, req) ==
    /\ Len(queue[p]) < MaxQLen
    /\ LET newId == <<p, Len(queue[p]) + 1>>
       IN  \E S \in SUBSET ExistingIds :
              LET preds == DownClosure(S \cup ProcIds(p))
              IN  /\ queue' = [queue EXCEPT ![p] = Append(@, req)]
                  /\ order' = order \cup { <<x, newId>> : x \in preds }

IssueRead(p, a)     == Issue(p, [op |-> "Rd", adr |-> a, val |-> NoVal])
IssueWrite(p, a, v) == Issue(p, [op |-> "Wr", adr |-> a, val |-> v])

Next ==
    \E p \in Proc, a \in Adr :
        \/ IssueRead(p, a)
        \/ \E v \in Val : IssueWrite(p, a, v)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* State constraint (bounded queues)                                       *)
-----------------------------------------------------------------------------

QueueConstraint == \A p \in Proc : Len(queue[p]) <= MaxQLen

-----------------------------------------------------------------------------
(* Invariants                                                              *)
-----------------------------------------------------------------------------

Irreflexive == \A x \in ExistingIds : <<x, x>> \notin order

Transitive ==
    \A r1, r2 \in order :
        (r1[2] = r2[1]) => (<<r1[1], r2[2]>> \in order)

StrictPartialOrder == Irreflexive /\ Transitive

ProgramOrder ==
    \A p \in Proc :
        \A i, j \in 1..Len(queue[p]) :
            (i < j) => (<< <<p, i>>, <<p, j>> >> \in order)

OrderInvariant == StrictPartialOrder /\ ProgramOrder

QueueBound == \A p \in Proc : Len(queue[p]) <= MaxQLen

NoSelfOrder == \A r \in order : r[1] # r[2]

-----------------------------------------------------------------------------
(* Temporal properties                                                     *)
-----------------------------------------------------------------------------

\* Once an ordering pair holds, it persists forever.
OrderMonotonic == [][order \subseteq order']_vars

\* Issued requests are never removed or altered.
QueuesGrowOnly ==
    [][\A p \in Proc :
          /\ Len(queue[p]) <= Len(queue'[p])
          /\ SubSeq(queue'[p], 1, Len(queue[p])) = queue[p]]_vars

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ OrderInvariant /\ QueueBound /\ NoSelfOrder)
THEOREM Spec => OrderMonotonic /\ QueuesGrowOnly
=============================================================================