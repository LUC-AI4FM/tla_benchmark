---- MODULE RequestQueue ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processors
          Reg,       \* set of registers
          Adr,       \* set of memory addresses
          Val,       \* set of values
          MaxQLen,   \* maximum length of a processor's request queue
          MaxReqs    \* maximum number of requests a processor may issue

ASSUME /\ MaxQLen \in Nat \ {0}
       /\ MaxReqs \in Nat \ {0}

(***************************************************************************)
(* Requests and request identifiers.                                       *)
(***************************************************************************)
Request == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

ReqId == Proc \X (1..MaxReqs)

QEntry == [req : Request, reg : Reg, id : ReqId]

VARIABLES reqQ,      \* reqQ[p] is the queue of requests issued by p
          reqOrder,  \* partial order on request identifiers
          reqCount   \* reqCount[p] is the number of requests issued by p

vars == <<reqQ, reqOrder, reqCount>>

(***************************************************************************)
(* Helper operators.                                                       *)
(***************************************************************************)
QIds(p) == { reqQ[p][i].id : i \in 1..Len(reqQ[p]) }

AllQIds == UNION { QIds(p) : p \in Proc }

IssuedIds == { <<p, n>> \in ReqId : n <= reqCount[p] }

(***************************************************************************)
(* Invariants.                                                             *)
(***************************************************************************)
TypeInvariant ==
  /\ reqQ \in [Proc -> Seq(QEntry)]
  /\ reqOrder \subseteq (ReqId \X ReqId)
  /\ reqCount \in [Proc -> 0..MaxReqs]

QueueLengthInvariant ==
  \A p \in Proc : Len(reqQ[p]) <= MaxQLen

\* Requests in p's queue are p's own issued requests, with distinct ids
QueueWellFormed ==
  \A p \in Proc :
     /\ \A i \in 1..Len(reqQ[p]) :
           /\ reqQ[p][i].id[1] = p
           /\ reqQ[p][i].id \in IssuedIds
     /\ \A i, j \in 1..Len(reqQ[p]) :
           (i # j) => (reqQ[p][i].id # reqQ[p][j].id)

\* reqOrder is an irreflexive, transitive (hence strict partial) order
\* over issued request identifiers
PartialOrderInvariant ==
  /\ \A r \in reqOrder : r[1] \in IssuedIds /\ r[2] \in IssuedIds
  /\ \A i \in ReqId : <<i, i>> \notin reqOrder
  /\ \A i, j, k \in ReqId :
        (<<i, j>> \in reqOrder /\ <<j, k>> \in reqOrder) => <<i, k>> \in reqOrder

\* Queue order is consistent with reqOrder
QueueOrderInvariant ==
  \A p \in Proc : \A i, j \in 1..Len(reqQ[p]) :
     (i < j) => <<reqQ[p][i].id, reqQ[p][j].id>> \in reqOrder

Invariant ==
  /\ TypeInvariant
  /\ QueueLengthInvariant
  /\ QueueWellFormed
  /\ PartialOrderInvariant
  /\ QueueOrderInvariant

(***************************************************************************)
(* Initial state.                                                          *)
(***************************************************************************)
Init ==
  /\ reqQ = [p \in Proc |-> << >>]
  /\ reqOrder = {}
  /\ reqCount = [p \in Proc |-> 0]

(***************************************************************************)
(* Actions.                                                                *)
(***************************************************************************)
\* Processor p issues request req for register reg.  The new request is
\* ordered after every request currently in p's queue and, to keep the
\* order transitive, after everything preceding those requests.
IssueRequest(p, req, reg) ==
  /\ Len(reqQ[p]) < MaxQLen
  /\ reqCount[p] < MaxReqs
  /\ LET newId == <<p, reqCount[p] + 1>>
         preds == QIds(p) \cup { r[1] : r \in { s \in reqOrder : s[2] \in QIds(p) } }
     IN  /\ reqQ' = [reqQ EXCEPT ![p] = Append(@, [req |-> req, reg |-> reg, id |-> newId])]
         /\ reqOrder' = reqOrder \cup { <<i, newId>> : i \in preds }
         /\ reqCount' = [reqCount EXCEPT ![p] = @ + 1]

\* The request at the head of p's queue is serviced and removed.
RetireRequest(p) ==
  /\ reqQ[p] # << >>
  /\ reqQ' = [reqQ EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<reqOrder, reqCount>>

Next ==
  \/ \E p \in Proc, req \in Request, reg \in Reg : IssueRequest(p, req, reg)
  \/ \E p \in Proc : RetireRequest(p)

Spec == Init /\ [][Next]_vars /\ \A p \in Proc : WF_vars(RetireRequest(p))

(***************************************************************************)
(* Liveness: every queued request is eventually removed from its queue.    *)
(***************************************************************************)
EventuallyRetired ==
  \A p \in Proc : \A id \in ReqId :
     (id \in QIds(p)) ~> (id \notin QIds(p))

THEOREM Spec => []Invariant
THEOREM Spec => EventuallyRetired
====