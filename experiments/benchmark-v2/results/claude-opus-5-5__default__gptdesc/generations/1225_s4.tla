------------------------------- MODULE RequestQueue -------------------------------
(***************************************************************************)
(* Models processors issuing read/write requests to registers.  Each      *)
(* processor p keeps a FIFO queue reqQ[p] of outstanding requests, and the *)
(* system maintains a global strict partial order reqOrder over request    *)
(* identifiers.                                                            *)
(*                                                                         *)
(* An earlier version of this spec had a bug.  IssueRequest added only the *)
(* ordering pair between the new request and the last request in the      *)
(* queue, so reqOrder was not transitively closed.  This version orders a  *)
(* new request after every request still in the issuing processor's queue, *)
(* which keeps reqOrder a well-formed partial order.                       *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processors
          Reg,       \* set of registers
          Val,       \* set of values that can be written
          QLen,      \* maximum length of a request queue
          MaxReqs    \* bound on requests issued per processor (for model checking)

ASSUME /\ QLen \in Nat \ {0}
       /\ MaxReqs \in Nat \ {0}

VARIABLES reqQ,      \* reqQ[p] : sequence of queued requests of processor p
          reqOrder,  \* set of pairs <<i, j>> of request ids: i precedes j
          issued     \* issued[p] : number of requests issued by p so far

vars == <<reqQ, reqOrder, issued>>

(***************************************************************************)
(* Request structure                                                       *)
(***************************************************************************)
Request == [op : {"Rd"}, adr : Reg] \cup [op : {"Wr"}, adr : Reg, val : Val]

ReqId == Proc \X (1..MaxReqs)

QEntry == [req : Request, id : ReqId]

QueueIds(p) == { reqQ[p][i].id : i \in 1..Len(reqQ[p]) }

AllQueuedIds == UNION { QueueIds(p) : p \in Proc }

BoundedSeq(S, n) == UNION { [1..k -> S] : k \in 0..n }

IsStrictPartialOrder(R, S) ==
    /\ R \subseteq S \X S
    /\ \A x \in S : <<x, x>> \notin R
    /\ \A x, y, z \in S :
          (<<x, y>> \in R /\ <<y, z>> \in R) => <<x, z>> \in R

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK ==
    /\ reqQ \in [Proc -> BoundedSeq(QEntry, QLen)]
    /\ reqOrder \subseteq ReqId \X ReqId
    /\ issued \in [Proc -> 0..MaxReqs]

QueueLengthOK == \A p \in Proc : Len(reqQ[p]) <= QLen

\* Every queued id belongs to its processor, ids are unique, and they
\* have actually been issued.
QueueIdsOK ==
    \A p \in Proc :
        /\ \A i \in 1..Len(reqQ[p]) :
              /\ reqQ[p][i].id[1] = p
              /\ reqQ[p][i].id[2] <= issued[p]
        /\ \A i, j \in 1..Len(reqQ[p]) :
              i # j => reqQ[p][i].id # reqQ[p][j].id

\* reqOrder is a strict partial order over the outstanding requests.
ReqOrderOK == IsStrictPartialOrder(reqOrder, AllQueuedIds)

\* Within each processor, reqOrder agrees with queue (program) order.
ReqOrderMatchesQueue ==
    \A p \in Proc : \A i, j \in 1..Len(reqQ[p]) :
        i < j => <<reqQ[p][i].id, reqQ[p][j].id>> \in reqOrder

Inv == /\ TypeOK
       /\ QueueLengthOK
       /\ QueueIdsOK
       /\ ReqOrderOK
       /\ ReqOrderMatchesQueue

(***************************************************************************)
(* Initial state and actions                                               *)
(***************************************************************************)
Init ==
    /\ reqQ = [p \in Proc |-> << >>]
    /\ reqOrder = {}
    /\ issued = [p \in Proc |-> 0]

IssueRequest(p, req) ==
    /\ Len(reqQ[p]) < QLen
    /\ issued[p] < MaxReqs
    /\ LET newId == <<p, issued[p] + 1>>
       IN  /\ reqQ' = [reqQ EXCEPT ![p] = Append(@, [req |-> req, id |-> newId])]
           /\ reqOrder' = reqOrder \cup { <<oid, newId>> : oid \in QueueIds(p) }
           /\ issued' = [issued EXCEPT ![p] = @ + 1]

\* The request at the head of p's queue is serviced and removed.
CompleteRequest(p) ==
    /\ Len(reqQ[p]) > 0
    /\ LET hid == Head(reqQ[p]).id
       IN  /\ reqQ' = [reqQ EXCEPT ![p] = Tail(@)]
           /\ reqOrder' = { pr \in reqOrder : pr[1] # hid /\ pr[2] # hid }
           /\ UNCHANGED issued

Next ==
    \/ \E p \in Proc, req \in Request : IssueRequest(p, req)
    \/ \E p \in Proc : CompleteRequest(p)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A p \in Proc : WF_vars(CompleteRequest(p))

(***************************************************************************)
(* Liveness: every issued request is eventually removed from its queue.    *)
(***************************************************************************)
EventuallyCompleted ==
    \A p \in Proc, n \in 1..MaxReqs :
        (<<p, n>> \in QueueIds(p)) ~> (<<p, n>> \notin QueueIds(p))

THEOREM Spec => []Inv
=============================================================================