---------------------------- MODULE RequestQueue ----------------------------
(***************************************************************************)
(* Models processors issuing requests to registers.  Each processor keeps  *)
(* a queue of outstanding requests (reqQ), and the system keeps a global   *)
(* partial order (reqOrder) over request identifiers.                      *)
(*                                                                         *)
(* NOTE: An earlier version of this spec contained a bug.  IssueRequest    *)
(* added only the pairs <<r, id>> for requests r in the issuing           *)
(* processor's queue.  It did not add the requests ordered before them,   *)
(* so reqOrder could fail to be transitive.  The invariant                 *)
(* ReqOrderIsPartialOrder catches that bug.                                *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,       \* set of processors
          Reg,        \* set of registers
          Val,        \* set of values that can be written
          MaxQLen,    \* bound on the length of each request queue
          MaxReqs     \* bound on the number of requests per processor

ASSUME /\ MaxQLen \in Nat \ {0}
       /\ MaxReqs \in Nat \ {0}

VARIABLES reqQ,       \* reqQ[p] : queue of [req |-> Request, id |-> ReqId]
          reqOrder,   \* partial order on request identifiers
          reqCount    \* reqCount[p] : number of requests issued by p

vars == <<reqQ, reqOrder, reqCount>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Structure of requests and request identifiers.                          *)
(***************************************************************************)
Request == [op : {"Rd"}, adr : Reg] \cup [op : {"Wr"}, adr : Reg, val : Val]

ReqId == Proc \X (1..MaxReqs)

QEntry == [req : Request, id : ReqId]

\* The set of identifiers of requests currently in p's queue
QIds(p) == {reqQ[p][i].id : i \in 1..Len(reqQ[p])}

\* The set of identifiers of all outstanding requests
AllIds == UNION {QIds(p) : p \in Proc}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants.                                                             *)
(***************************************************************************)
TypeOK ==
  /\ reqQ \in [Proc -> Seq(QEntry)]
  /\ reqOrder \subseteq ReqId \X ReqId
  /\ reqCount \in [Proc -> 0..MaxReqs]

QueueLengthOK == \A p \in Proc : Len(reqQ[p]) <= MaxQLen

\* An irreflexive and transitive relation, which is a strict partial order
IsPartialOrder(R, S) ==
  /\ R \subseteq S \X S
  /\ \A x \in S : <<x, x>> \notin R
  /\ \A x, y, z \in S : (<<x, y>> \in R /\ <<y, z>> \in R) => <<x, z>> \in R

ReqOrderIsPartialOrder == IsPartialOrder(reqOrder, AllIds)

\* Requests in a processor's queue are totally ordered by reqOrder,
\* consistent with their queue positions.
QueueConsistentWithOrder ==
  \A p \in Proc :
    \A i, j \in 1..Len(reqQ[p]) :
      i < j => <<reqQ[p][i].id, reqQ[p][j].id>> \in reqOrder

\* Request identifiers are unique across all queues
UniqueIds ==
  \A p, q \in Proc :
    \A i \in 1..Len(reqQ[p]), j \in 1..Len(reqQ[q]) :
      (reqQ[p][i].id = reqQ[q][j].id) => (p = q /\ i = j)

Invariants ==
  /\ TypeOK
  /\ QueueLengthOK
  /\ ReqOrderIsPartialOrder
  /\ QueueConsistentWithOrder
  /\ UniqueIds

-----------------------------------------------------------------------------
(***************************************************************************)
(* Initial state and actions.                                              *)
(***************************************************************************)
Init ==
  /\ reqQ = [p \in Proc |-> << >>]
  /\ reqOrder = {}
  /\ reqCount = [p \in Proc |-> 0]

(***************************************************************************)
(* Processor p issues request req.  The new request is ordered after every *)
(* request in p's queue and after every request that precedes one of them. *)
(* Because the new request is maximal, this keeps reqOrder transitive.     *)
(***************************************************************************)
IssueRequest(p, req) ==
  /\ Len(reqQ[p]) < MaxQLen
  /\ reqCount[p] < MaxReqs
  /\ LET id    == <<p, reqCount[p] + 1>>
         preds == QIds(p) \cup {x \in AllIds : \E q \in QIds(p) : <<x, q>> \in reqOrder}
     IN  /\ reqQ' = [reqQ EXCEPT ![p] = Append(@, [req |-> req, id |-> id])]
         /\ reqOrder' = reqOrder \cup {<<x, id>> : x \in preds}
         /\ reqCount' = [reqCount EXCEPT ![p] = @ + 1]

(***************************************************************************)
(* The request at the head of p's queue is serviced and removed.  It and   *)
(* every pair involving it are removed from reqOrder.  Removing an element *)
(* from a partial order leaves a partial order.                            *)
(***************************************************************************)
ServiceRequest(p) ==
  /\ Len(reqQ[p]) > 0
  /\ LET id == Head(reqQ[p]).id
     IN  /\ \A x \in AllIds : <<x, id>> \notin reqOrder
         /\ reqQ' = [reqQ EXCEPT ![p] = Tail(@)]
         /\ reqOrder' = {pr \in reqOrder : pr[1] # id /\ pr[2] # id}
         /\ UNCHANGED reqCount

Next ==
  \/ \E p \in Proc, req \in Request : IssueRequest(p, req)
  \/ \E p \in Proc : ServiceRequest(p)

Spec == Init /\ [][Next]_vars /\ \A p \in Proc : WF_vars(ServiceRequest(p))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness: every outstanding request is eventually serviced.             *)
(***************************************************************************)
EventuallyServiced ==
  \A p \in Proc : \A n \in 1..MaxReqs :
    (<<p, n>> \in AllIds) ~> (<<p, n>> \notin AllIds)

QueuesEventuallyDrain ==
  \A p \in Proc : (Len(reqQ[p]) > 0) ~> (Len(reqQ[p]) = 0)

THEOREM Spec => []Invariants
=============================================================================