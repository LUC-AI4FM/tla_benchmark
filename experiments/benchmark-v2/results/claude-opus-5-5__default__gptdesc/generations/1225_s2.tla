-------------------------- MODULE RequestOrdering --------------------------
(***************************************************************************)
(* Models processors that issue requests to registers.  Each processor     *)
(* keeps a bounded queue of pending requests (reqQ), and the system keeps  *)
(* a global strict partial order (reqOrder) over request identifiers.      *)
(* An earlier version of this spec had a bug: a new request was ordered    *)
(* only after the requests in its own queue, not after their transitive    *)
(* predecessors, so reqOrder could stop being transitive.  The invariants  *)
(* below are meant to catch bugs like that.                                *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processors
          Reg,       \* set of registers
          MaxQLen,   \* maximum length of a processor's request queue
          MaxReqs    \* maximum number of requests a processor may issue

ASSUME /\ MaxQLen \in Nat \ {0}
       /\ MaxReqs \in Nat \ {0}

VARIABLES reqQ,      \* reqQ[p] : sequence of pending requests of processor p
          reqOrder,  \* set of pairs <<i, j>> meaning request i precedes j
          reqCount   \* reqCount[p] : number of requests p has issued so far

vars == <<reqQ, reqOrder, reqCount>>

(***************************************************************************)
(* Requests and request identifiers                                        *)
(***************************************************************************)
reqId == Proc \X (1..MaxReqs)

Request == [proc : Proc, reg : Reg, op : {"Rd", "Wr"}]

QEntry == [req : Request, id : reqId]

QIds(p) == {reqQ[p][i].id : i \in 1..Len(reqQ[p])}

PendingIds == UNION {QIds(p) : p \in Proc}

InQueue(p, n) == <<p, n>> \in QIds(p)

BoundedSeq(S, n) == UNION {[1..k -> S] : k \in 0..n}

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK ==
    /\ reqQ \in [Proc -> BoundedSeq(QEntry, MaxQLen)]
    /\ reqOrder \subseteq reqId \X reqId
    /\ reqCount \in [Proc -> 0..MaxReqs]

QLenOK == \A p \in Proc : Len(reqQ[p]) <= MaxQLen

Irreflexive == \A i \in reqId : <<i, i>> \notin reqOrder

Transitive ==
    \A i, j, k \in reqId :
        (<<i, j>> \in reqOrder /\ <<j, k>> \in reqOrder) => <<i, k>> \in reqOrder

Antisymmetric ==
    \A i, j \in reqId : ~(<<i, j>> \in reqOrder /\ <<j, i>> \in reqOrder)

PartialOrderOK == Irreflexive /\ Transitive /\ Antisymmetric

OrderOnPendingOnly == reqOrder \subseteq PendingIds \X PendingIds

QueueRespectsOrder ==
    \A p \in Proc :
        \A i, j \in 1..Len(reqQ[p]) :
            i < j => <<reqQ[p][i].id, reqQ[p][j].id>> \in reqOrder

QueueEntriesWellFormed ==
    \A p \in Proc :
        \A i \in 1..Len(reqQ[p]) :
            /\ reqQ[p][i].req.proc = p
            /\ reqQ[p][i].id[1] = p
            /\ reqQ[p][i].id[2] <= reqCount[p]

Inv ==
    /\ TypeOK
    /\ QLenOK
    /\ PartialOrderOK
    /\ OrderOnPendingOnly
    /\ QueueRespectsOrder
    /\ QueueEntriesWellFormed

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
    /\ reqQ = [p \in Proc |-> << >>]
    /\ reqOrder = {}
    /\ reqCount = [p \in Proc |-> 0]

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
IssueRequest(p, r, o) ==
    /\ Len(reqQ[p]) < MaxQLen
    /\ reqCount[p] < MaxReqs
    /\ LET newId == <<p, reqCount[p] + 1>>
           req   == [proc |-> p, reg |-> r, op |-> o]
           preds == QIds(p) \cup {pr[1] : pr \in {x \in reqOrder : x[2] \in QIds(p)}}
       IN  /\ reqQ' = [reqQ EXCEPT ![p] = Append(@, [req |-> req, id |-> newId])]
           /\ reqOrder' = reqOrder \cup {<<i, newId>> : i \in preds}
           /\ reqCount' = [reqCount EXCEPT ![p] = @ + 1]

CompleteRequest(p) ==
    /\ Len(reqQ[p]) > 0
    /\ LET hid == Head(reqQ[p]).id
       IN  /\ reqQ' = [reqQ EXCEPT ![p] = Tail(@)]
           /\ reqOrder' = {pr \in reqOrder : pr[1] # hid /\ pr[2] # hid}
           /\ UNCHANGED reqCount

Next ==
    \/ \E p \in Proc, r \in Reg, o \in {"Rd", "Wr"} : IssueRequest(p, r, o)
    \/ \E p \in Proc : CompleteRequest(p)

Fairness == \A p \in Proc : WF_vars(CompleteRequest(p))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Liveness: every issued request is eventually removed from its queue.    *)
(***************************************************************************)
EventuallyCompleted ==
    \A p \in Proc, n \in 1..MaxReqs : InQueue(p, n) ~> ~InQueue(p, n)

THEOREM Spec => []Inv
=============================================================================