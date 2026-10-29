---------------------------- MODULE ReqOrderTest ----------------------------
(***************************************************************************)
(* A test case (one that caught a bug in an early version of TLC) that     *)
(* models a simplified request-ordering system for a multiprocessor        *)
(* memory architecture.                                                    *)
(*                                                                         *)
(* reqQ[p]  : the sequence of requests issued by processor p.              *)
(* reqOrder : a binary relation over request identifiers that captures     *)
(*            the global ordering of requests.                             *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS Reg, Adr, Val, Proc

VARIABLES reqQ, reqOrder

vars == <<reqQ, reqOrder>>

---------------------------------------------------------------------------
(***************************************************************************)
(* Requests.                                                               *)
(***************************************************************************)
Request ==
       [op : {"Rd"}, adr : Adr, reg : Reg]
  \cup [op : {"Wr"}, adr : Adr, val : Val]

RegRecord == [reg : Reg]

(***************************************************************************)
(* A request identifier pairs a processor with an index into that          *)
(* processor's request queue.                                              *)
(***************************************************************************)
ReqIdOf(q) == { [proc |-> p, idx |-> i] : p \in Proc, i \in 1..Len(q[p]) }

reqId == ReqIdOf(reqQ)

(***************************************************************************)
(* A good request order is transitive, irreflexive, and respects program   *)
(* order: an earlier request of a processor precedes a later one.          *)
(***************************************************************************)
GoodReqOrder(ids, ro) ==
  /\ \A a, b, c \in ids :
        (<<a, b>> \in ro /\ <<b, c>> \in ro) => (<<a, c>> \in ro)
  /\ \A a \in ids : <<a, a>> \notin ro
  /\ \A a, b \in ids :
        (a.proc = b.proc /\ a.idx < b.idx) => (<<a, b>> \in ro)

---------------------------------------------------------------------------
TypeInvariant ==
  /\ reqQ \in [Proc -> Seq(Request \cup RegRecord)]
  /\ reqOrder \subseteq (reqId \X reqId)

Init ==
  /\ reqQ = [p \in Proc |-> << >>]
  /\ reqOrder = {}

(***************************************************************************)
(* Nondeterministically extend the request order so that it is a          *)
(* superset of the old order, a subset of the new request-id cross         *)
(* product, and a good request order.                                      *)
(***************************************************************************)
UpdateReqOrder ==
  LET newIds == ReqIdOf(reqQ')
  IN  \E ro \in SUBSET (newIds \X newIds) :
         /\ reqOrder \subseteq ro
         /\ GoodReqOrder(newIds, ro)
         /\ reqOrder' = ro

IssueRequest ==
  \E p \in Proc, r \in Reg :
     /\ reqQ' = [reqQ EXCEPT ![p] = Append(@, [reg |-> r])]
     /\ UpdateReqOrder

Next == IssueRequest

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(***************************************************************************)
(* Model constraint: each processor's queue has fewer than two entries.    *)
(***************************************************************************)
Constraint == \A p \in Proc : Len(reqQ[p]) < 2

THEOREM Spec => []TypeInvariant
=============================================================================