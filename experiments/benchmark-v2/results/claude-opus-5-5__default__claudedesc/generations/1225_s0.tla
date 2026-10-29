------------------------------- MODULE ReqOrderTest -------------------------------
(***************************************************************************)
(* TLC test case (exposed a bug in TLC version 1.03).                      *)
(* A simplified multiprocessor memory request system: processors issue     *)
(* read/write requests that are tracked in per-processor queues and are    *)
(* ordered by a global order relation reqOrder.                            *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS Proc,      \* set of processors
          Reg,       \* set of registers
          Request    \* set of requests (e.g. read / write requests)

VARIABLES reqQ, reqOrder

vars == <<reqQ, reqOrder>>

(***************************************************************************)
(* A request entry in a queue: a request tagged with a register.           *)
(***************************************************************************)
ReqEntry == [req : Request, reg : Reg]

(***************************************************************************)
(* Request identifiers: a processor paired with an index into that         *)
(* processor's queue.                                                      *)
(***************************************************************************)
reqIdOf(q) == UNION { { <<p, i>> : i \in DOMAIN q[p] } : p \in Proc }

reqId == reqIdOf(reqQ)

(***************************************************************************)
(* The ordering relation between two request identifiers.                  *)
(***************************************************************************)
r1 \prec r2 == <<r1, r2>> \in reqOrder

(***************************************************************************)
(* R is a strict partial order on the request ids of queue q that is       *)
(* consistent with program order.                                          *)
(***************************************************************************)
GoodReqOrderOf(R, q) ==
  LET ids == reqIdOf(q)
      Before(a, b) == <<a, b>> \in R
  IN  /\ R \subseteq ids \X ids
      \* transitive
      /\ \A a, b, c \in ids : Before(a, b) /\ Before(b, c) => Before(a, c)
      \* irreflexive
      /\ \A a \in ids : ~ Before(a, a)
      \* consistent with program order
      /\ \A p \in Proc :
           \A i, j \in DOMAIN q[p] :
             (i < j) => Before(<<p, i>>, <<p, j>>)

GoodReqOrder == GoodReqOrderOf(reqOrder, reqQ)

-----------------------------------------------------------------------------

TypeInvariant ==
  /\ reqQ \in [Proc -> Seq(ReqEntry)]
  /\ reqOrder \subseteq (reqId \X reqId)

Init ==
  /\ reqQ = [p \in Proc |-> << >>]
  /\ reqOrder = {}

(***************************************************************************)
(* Processor p issues request req for register r.  The request is appended *)
(* to p's queue and reqOrder is non-deterministically extended in any way  *)
(* that preserves the existing order and satisfies GoodReqOrder.           *)
(***************************************************************************)
IssueRequest(p, req, r) ==
  LET newQ   == [reqQ EXCEPT ![p] = Append(@, [req |-> req, reg |-> r])]
      newIds == reqIdOf(newQ)
  IN  /\ reqQ' = newQ
      /\ \E R \in SUBSET (newIds \X newIds) :
            /\ reqOrder \subseteq R
            /\ GoodReqOrderOf(R, newQ)
            /\ reqOrder' = R

Next == \E p \in Proc, r \in Reg, req \in Request : IssueRequest(p, req, r)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* State constraint: at most one pending request per processor.            *)
(***************************************************************************)
Constraint == \A p \in Proc : Len(reqQ[p]) <= 1

THEOREM Spec => []TypeInvariant
=============================================================================