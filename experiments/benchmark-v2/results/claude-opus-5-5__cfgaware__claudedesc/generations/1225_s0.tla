---------------------------- MODULE MemoryRequests ----------------------------
(***************************************************************************)
(* A TLC test case (noted as exposing a bug in TLC version 1.03).          *)
(* It models a simplified multiprocessor memory request system.            *)
(* Processors issue read and write requests. The requests are kept in      *)
(* per-processor queues and ordered by a global order relation reqOrder.   *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS Reg, Adr, Val, Proc

VARIABLES reqQ, reqOrder

vars == <<reqQ, reqOrder>>

-----------------------------------------------------------------------------
Request ==
       [type : {"Rd"}, adr : Adr]
  \cup [type : {"Wr"}, adr : Adr, val : Val]

ReqEntry == [req : Request, reg : Reg]

(* A request identifier pairs a processor with an index into its queue. *)
ReqIdUniverse == Proc \X Nat

ReqIds(q) == UNION { { <<p, i>> : i \in 1..Len(q[p]) } : p \in Proc }

reqId == ReqIds(reqQ)

r1 \prec r2 == <<r1, r2>> \in reqOrder

GoodReqOrder ==
  /\ \A r1, r2, r3 \in reqId :
        (r1 \prec r2) /\ (r2 \prec r3) => (r1 \prec r3)
  /\ \A r \in reqId : ~(r \prec r)
  /\ \A p \in Proc :
        \A i, j \in 1..Len(reqQ[p]) :
           (i < j) => (<<p, i>> \prec <<p, j>>)

-----------------------------------------------------------------------------
TypeInvariant ==
  /\ reqQ \in [Proc -> Seq(ReqEntry)]
  /\ reqOrder \subseteq (ReqIdUniverse \X ReqIdUniverse)

Init ==
  /\ reqQ = [p \in Proc |-> << >>]
  /\ reqOrder = {}

IssueRequest(proc, req, reg) ==
  /\ reqQ' = [reqQ EXCEPT ![proc] = Append(@, [req |-> req, reg |-> reg])]
  /\ \E ro \in SUBSET (ReqIds(reqQ') \X ReqIds(reqQ')) :
        /\ reqOrder \subseteq ro
        /\ reqOrder' = ro
        /\ GoodReqOrder'

Next ==
  \E proc \in Proc, reg \in Reg, req \in Request :
     IssueRequest(proc, req, reg)

Spec == Init /\ [][Next]_vars

Constraint == \A p \in Proc : Len(reqQ[p]) <= 1
=============================================================================