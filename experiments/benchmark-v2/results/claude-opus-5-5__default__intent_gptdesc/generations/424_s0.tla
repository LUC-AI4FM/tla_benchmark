------------------------------ MODULE RequestOrder ------------------------------
(***************************************************************************)
(* A fixed set of processors asynchronously issue read or write requests   *)
(* into bounded per-processor queues. A global strict partial order on     *)
(* issued request identifiers is maintained. It extends each processor's   *)
(* program order and only ever grows.                                      *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processors
          Adr,       \* set of memory addresses
          Val,       \* set of data values
          QLen       \* bound on the length of each processor's queue

ASSUME QLen \in Nat /\ QLen > 0
ASSUME Proc # {}

VARIABLES reqQ,      \* reqQ[p] : sequence of requests issued by processor p
          ord        \* set of pairs <<id1, id2>> meaning id1 precedes id2

vars == <<reqQ, ord>>

---------------------------------------------------------------------------
(* Requests and request identifiers                                        *)

RdReq == [op : {"Rd"}, adr : Adr]
WrReq == [op : {"Wr"}, adr : Adr, val : Val]
Request == RdReq \cup WrReq

\* A request identity is the issuing processor and its position in its queue.
ReqId == Proc \X (1..QLen)

BoundedSeq(S, n) == UNION { [1..k -> S] : k \in 0..n }

\* Identifiers of all requests issued so far
IssuedIds == { <<p, i>> : p \in Proc, i \in 1..Len(reqQ[p]) }

\* Predecessors and successors of an identifier in the current order
Pred(x) == { y \in ReqId : <<y, x>> \in ord }
Succ(x) == { y \in ReqId : <<x, y>> \in ord }

---------------------------------------------------------------------------
(* Properties of relations                                                 *)

Irreflexive(R) == \A x \in ReqId : <<x, x>> \notin R

Transitive(R) ==
  \A a, b, c \in ReqId :
     (<<a, b>> \in R /\ <<b, c>> \in R) => <<a, c>> \in R

StrictPartialOrder(R) == Irreflexive(R) /\ Transitive(R)

\* The order respects every processor's program order
RespectsProgramOrder(R) ==
  \A p \in Proc :
     \A i, j \in 1..Len(reqQ[p]) :
        i < j => <<<<p, i>>, <<p, j>>>> \in R

---------------------------------------------------------------------------
(* Initial state                                                           *)

Init ==
  /\ reqQ = [p \in Proc |-> << >>]
  /\ ord  = {}

---------------------------------------------------------------------------
(* Actions                                                                 *)

(* Processor p appends request r to its own queue, subject to the bound.   *)
(* The new identifier is ordered after all earlier requests of p and,      *)
(* for transitivity, after all their predecessors. The new identifier has  *)
(* no successors, so the result stays a strict partial order.              *)
Issue(p, r) ==
  /\ Len(reqQ[p]) < QLen
  /\ LET newId == <<p, Len(reqQ[p]) + 1>>
         own   == { <<p, j>> : j \in 1..Len(reqQ[p]) }
         below == own \cup UNION { Pred(x) : x \in own }
     IN  /\ reqQ' = [reqQ EXCEPT ![p] = Append(@, r)]
         /\ ord'  = ord \cup { <<x, newId>> : x \in below }

IssueAny(p) == \E r \in Request : Issue(p, r)

(* Add a new ordering relation a -> b between two issued requests. It is   *)
(* closed transitively, and is allowed only if irreflexivity is kept,      *)
(* that is, if b does not already precede or equal a.                     *)
AddOrder(a, b) ==
  /\ a \in IssuedIds
  /\ b \in IssuedIds
  /\ a # b
  /\ <<a, b>> \notin ord
  /\ <<b, a>> \notin ord
  /\ ord' = ord \cup { <<x, y>> : x \in {a} \cup Pred(a),
                                  y \in {b} \cup Succ(b) }
  /\ UNCHANGED reqQ

Next ==
  \/ \E p \in Proc : IssueAny(p)
  \/ \E a, b \in ReqId : AddOrder(a, b)

---------------------------------------------------------------------------
(* Specification with minimal fairness: each processor keeps issuing      *)
(* requests while its queue bound allows.                                  *)

Fairness == \A p \in Proc : WF_vars(IssueAny(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety invariants                                                       *)

TypeOK ==
  /\ reqQ \in [Proc -> BoundedSeq(Request, QLen)]
  /\ ord \subseteq ReqId \X ReqId

QueueBound == \A p \in Proc : Len(reqQ[p]) <= QLen

OrderOnIssued == ord \subseteq IssuedIds \X IssuedIds

OrderIsStrictPartialOrder == StrictPartialOrder(ord)

OrderExtendsProgramOrder == RespectsProgramOrder(ord)

Inv ==
  /\ TypeOK
  /\ QueueBound
  /\ OrderOnIssued
  /\ OrderIsStrictPartialOrder
  /\ OrderExtendsProgramOrder

(* Monotonic growth: no order relation is removed, and queues only grow   *)
(* by appending, so existing request identities never change.             *)
OrderMonotonic == [][ord \subseteq ord']_vars

QueuesOnlyAppend ==
  [][\A p \in Proc :
        /\ Len(reqQ[p]) <= Len(reqQ'[p])
        /\ SubSeq(reqQ'[p], 1, Len(reqQ[p])) = reqQ[p]]_vars

---------------------------------------------------------------------------
(* Minimal liveness: every processor eventually fills its queue.          *)

EventuallyFull == \A p \in Proc : <>(Len(reqQ[p]) = QLen)

---------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => OrderMonotonic /\ QueuesOnlyAppend
THEOREM Spec => EventuallyFull
=============================================================================