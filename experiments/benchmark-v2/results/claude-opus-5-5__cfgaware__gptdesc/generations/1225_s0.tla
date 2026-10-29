---------------------------- MODULE RequestOrder ----------------------------
(***************************************************************************)
(* Models processors issuing requests to registers.  Each processor keeps  *)
(* a queue of its outstanding requests (reqQ), and the system maintains a  *)
(* global partial order (reqOrder) over request identifiers.  An earlier   *)
(* version of this specification had a bug in how the order was extended  *)
(* when a request was issued; this version checks that the order remains  *)
(* a well-formed partial order and that the queues are well-typed.         *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Reg, Adr, Val, Proc

VARIABLES reqQ, reqOrder, reqId

vars == <<reqQ, reqOrder, reqId>>

-----------------------------------------------------------------------------
(* Request identifiers are positive naturals handed out in issue order.    *)
ReqIdSet == 1..reqId

Request ==
  [proc : Proc, reg : Reg, adr : Adr, op : {"Rd", "Wr"}, val : Val, id : Nat]

(* Elements of a sequence as a set. *)
Elems(s) == {s[i] : i \in 1..Len(s)}

(* All request ids currently held in some queue. *)
QueuedIds == UNION {{q.id : q \in Elems(reqQ[p])} : p \in Proc}

-----------------------------------------------------------------------------
(* Partial-order properties over a set S. *)
IsReflexive(R, S)     == \A x \in S : <<x, x>> \in R
IsAntisymmetric(R, S) == \A x, y \in S : (<<x, y>> \in R /\ <<y, x>> \in R) => x = y
IsTransitive(R, S)    == \A x, y, z \in S :
                            (<<x, y>> \in R /\ <<y, z>> \in R) => <<x, z>> \in R
IsPartialOrder(R, S)  == /\ R \subseteq S \X S
                         /\ IsReflexive(R, S)
                         /\ IsAntisymmetric(R, S)
                         /\ IsTransitive(R, S)

-----------------------------------------------------------------------------
TypeInvariant ==
  /\ reqId \in Nat
  /\ reqQ \in [Proc -> Seq(Request)]
  /\ \A p \in Proc : \A i \in 1..Len(reqQ[p]) :
        /\ reqQ[p][i].proc = p
        /\ reqQ[p][i].id \in ReqIdSet
  /\ reqOrder \subseteq ReqIdSet \X ReqIdSet

OrderInvariant ==
  /\ IsPartialOrder(reqOrder, ReqIdSet)
  (* Requests in a processor's queue are ordered by program order. *)
  /\ \A p \in Proc : \A i, j \in 1..Len(reqQ[p]) :
        i < j => <<reqQ[p][i].id, reqQ[p][j].id>> \in reqOrder

-----------------------------------------------------------------------------
Init ==
  /\ reqQ = [p \in Proc |-> << >>]
  /\ reqOrder = {}
  /\ reqId = 0

(* Processor p issues a new request.  The new request is ordered after     *)
(* every request ordered before or equal to any request currently in p's   *)
(* queue, which keeps reqOrder transitively closed.                        *)
IssueRequest(p, r, a, o, v) ==
  LET newId == reqId + 1
      req   == [proc |-> p, reg |-> r, adr |-> a, op |-> o, val |-> v, id |-> newId]
      preds == {x \in ReqIdSet :
                  \E q \in Elems(reqQ[p]) : <<x, q.id>> \in reqOrder}
  IN  /\ reqQ' = [reqQ EXCEPT ![p] = Append(@, req)]
      /\ reqOrder' = reqOrder \cup {<<x, newId>> : x \in preds}
                              \cup {<<newId, newId>>}
      /\ reqId' = newId

(* Processor p completes the request at the head of its queue. *)
CompleteRequest(p) ==
  /\ reqQ[p] # << >>
  /\ reqQ' = [reqQ EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<reqOrder, reqId>>

Next ==
  \/ \E p \in Proc, r \in Reg, a \in Adr, o \in {"Rd", "Wr"}, v \in Val :
        IssueRequest(p, r, a, o, v)
  \/ \E p \in Proc : CompleteRequest(p)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* State constraint bounding queue lengths and number of issued requests. *)
MaxQLen == 2
MaxReqs == 3

Constraint ==
  /\ \A p \in Proc : Len(reqQ[p]) =< MaxQLen
  /\ reqId =< MaxReqs

THEOREM Spec => [](TypeInvariant /\ OrderInvariant)
=============================================================================