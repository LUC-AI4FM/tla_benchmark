------------------------------- MODULE RequestOrdering -------------------------------
(***************************************************************************)
(* A model of request issuing in a multiprocessor / multi-agent system.    *)
(* Each processor issues requests (reads / writes) to registers.  Every     *)
(* processor has a bounded queue of outstanding requests (reqQ), and the    *)
(* system maintains a global partial order (reqOrder) over request          *)
(* identifiers.  An earlier version of this spec contained a bug: issuing   *)
(* a request did not add the transitive predecessors of the issuing         *)
(* processor's earlier requests to reqOrder, so reqOrder could stop being   *)
(* transitive.  The invariants below are meant to catch that kind of bug.   *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processors
          Reg,       \* set of registers
          Val,       \* set of values that can be written
          MaxQLen,   \* maximum length of a processor's request queue
          MaxReqs    \* maximum number of requests each processor may issue

ASSUME /\ MaxQLen \in Nat \ {0}
       /\ MaxReqs \in Nat \ {0}

NoVal == CHOOSE v : v \notin Val

VARIABLES reqQ,      \* reqQ[p] : queue of outstanding requests of processor p
          reqOrder,  \* global partial order on request identifiers
          nextId     \* nextId[p] : index of the next request p will issue

vars == <<reqQ, reqOrder, nextId>>

(***************************************************************************)
(* Request identifiers and requests.                                      *)
(***************************************************************************)
ReqId == Proc \X (1..MaxReqs)

Request == [id : ReqId, reg : Reg, op : {"Rd"}, val : {NoVal}]
             \cup
           [id : ReqId, reg : Reg, op : {"Wr"}, val : Val]

\* Identifiers already issued by processor p
IssuedBy(p) == {<<p, k>> : k \in 1..(nextId[p] - 1)}

Issued == UNION {IssuedBy(p) : p \in Proc}

\* Identifiers of requests still pending in some queue
QIds(p) == {reqQ[p][k].id : k \in 1..Len(reqQ[p])}
PendingIds == UNION {QIds(p) : p \in Proc}

\* Down-set and up-set of an identifier with respect to reqOrder
Down(i) == {i} \cup {a \in ReqId : <<a, i>> \in reqOrder}
Up(j)   == {j} \cup {b \in ReqId : <<j, b>> \in reqOrder}

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK ==
  /\ reqQ \in [Proc -> Seq(Request)]
  /\ reqOrder \subseteq ReqId \X ReqId
  /\ nextId \in [Proc -> 1..(MaxReqs + 1)]

QueueLengthOK == \A p \in Proc : Len(reqQ[p]) <= MaxQLen

\* reqOrder is a (strict) partial order over issued identifiers
Irreflexive  == \A i \in ReqId : <<i, i>> \notin reqOrder
Transitive   == \A i, j, k \in ReqId :
                   (<<i, j>> \in reqOrder /\ <<j, k>> \in reqOrder)
                      => <<i, k>> \in reqOrder
Antisymmetric == \A i, j \in ReqId :
                   (<<i, j>> \in reqOrder) => (<<j, i>> \notin reqOrder)
OrderOverIssued == \A pr \in reqOrder : pr[1] \in Issued /\ pr[2] \in Issued

ReqOrderIsPartialOrder ==
  Irreflexive /\ Transitive /\ Antisymmetric /\ OrderOverIssued

\* Each queue respects program order and the global request order
QueueOrdered ==
  \A p \in Proc :
    \A k, l \in 1..Len(reqQ[p]) :
      k < l => /\ reqQ[p][k].id[2] < reqQ[p][l].id[2]
               /\ <<reqQ[p][k].id, reqQ[p][l].id>> \in reqOrder

\* Queued requests belong to their processor and have been issued
QueueWellFormed ==
  \A p \in Proc :
    \A k \in 1..Len(reqQ[p]) :
      /\ reqQ[p][k].id[1] = p
      /\ reqQ[p][k].id \in IssuedBy(p)

Inv == /\ TypeOK
       /\ QueueLengthOK
       /\ ReqOrderIsPartialOrder
       /\ QueueOrdered
       /\ QueueWellFormed

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
  /\ reqQ = [p \in Proc |-> << >>]
  /\ reqOrder = {}
  /\ nextId = [p \in Proc |-> 1]

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* Processor p issues a new request req.  The new request is ordered after
\* every request p has already issued, and (to keep reqOrder transitive)
\* after everything that precedes those requests.
IssueRequest(p, req) ==
  /\ nextId[p] <= MaxReqs
  /\ Len(reqQ[p]) < MaxQLen
  /\ req.id = <<p, nextId[p]>>
  /\ LET preds == UNION {Down(i) : i \in IssuedBy(p)}
     IN  reqOrder' = reqOrder \cup {<<a, req.id>> : a \in preds}
  /\ reqQ' = [reqQ EXCEPT ![p] = Append(@, req)]
  /\ nextId' = [nextId EXCEPT ![p] = @ + 1]

Issue(p) ==
  \E r \in Reg :
    \/ IssueRequest(p, [id |-> <<p, nextId[p]>>, reg |-> r,
                        op |-> "Rd", val |-> NoVal])
    \/ \E v \in Val :
         IssueRequest(p, [id |-> <<p, nextId[p]>>, reg |-> r,
                          op |-> "Wr", val |-> v])

\* Order two previously unordered issued requests i before j, closing
\* the relation transitively.
OrderRequests(i, j) ==
  /\ i \in Issued
  /\ j \in Issued
  /\ i # j
  /\ <<i, j>> \notin reqOrder
  /\ <<j, i>> \notin reqOrder
  /\ reqOrder' = reqOrder \cup {<<a, b>> : a \in Down(i), b \in Up(j)}
  /\ UNCHANGED <<reqQ, nextId>>

\* The head of p's queue is served when no pending request precedes it.
ServeRequest(p) ==
  /\ reqQ[p] # << >>
  /\ \A i \in PendingIds : <<i, Head(reqQ[p]).id>> \notin reqOrder
  /\ reqQ' = [reqQ EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<reqOrder, nextId>>

Serve == \E p \in Proc : ServeRequest(p)

Next ==
  \/ \E p \in Proc : Issue(p)
  \/ \E i, j \in ReqId : OrderRequests(i, j)
  \/ Serve

Spec == Init /\ [][Next]_vars /\ WF_vars(Serve)

(***************************************************************************)
(* Liveness: every pending request is eventually served.                   *)
(***************************************************************************)
EventuallyServed ==
  \A i \in ReqId : (i \in PendingIds) ~> (i \notin PendingIds)

THEOREM Spec => []Inv
THEOREM Spec => EventuallyServed
=======================================================================================