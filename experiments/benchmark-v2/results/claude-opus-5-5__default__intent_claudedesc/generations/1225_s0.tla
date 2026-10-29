--------------------------- MODULE MPRequestOrder ---------------------------
(***************************************************************************)
(* A simplified multiprocessor request-ordering system.  Each processor    *)
(* keeps a queue of issued requests (address, value, operation).  A global *)
(* strict partial order over request identifiers is kept.  It must respect *)
(* per-processor program order.  The only action is a processor issuing a *)
(* new request.  That action appends to its queue and nondeterministically *)
(* extends the global order.  The spec serves as a regression test for the *)
(* TLA+ tools, so the main property checked is a type invariant.           *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processors
          Reg,       \* set of registers
          Adr,       \* set of addresses
          Val,       \* set of values
          MaxQLen    \* bound on queue length (for the state constraint)

ASSUME /\ MaxQLen \in Nat
       /\ Proc # {}

VARIABLES reqQ,      \* reqQ[p] : sequence of requests issued by processor p
          reqOrder   \* global order: a set of pairs of request identifiers

vars == <<reqQ, reqOrder>>

-----------------------------------------------------------------------------
Ops == {"Rd", "Wr"}

Request == [adr : Adr, val : Val, op : Ops]

ReqId == [proc : Proc, idx : Nat \ {0}]

(* The identifiers of all requests currently in the queues *)
CurrentIds == { [proc |-> p, idx |-> i] : p \in Proc, i \in 1..Len(reqQ[p]) }

IsIrreflexive(R, S) == \A x \in S : <<x, x>> \notin R

IsTransitive(R, S) ==
    \A x, y, z \in S : (<<x, y>> \in R /\ <<y, z>> \in R) => <<x, z>> \in R

IsStrictPartialOrder(R, S) == IsIrreflexive(R, S) /\ IsTransitive(R, S)

RespectsProgramOrder(R, S) ==
    \A x, y \in S : (x.proc = y.proc /\ x.idx < y.idx) => <<x, y>> \in R

GoodOrder(R, S) ==
    /\ R \subseteq S \X S
    /\ IsStrictPartialOrder(R, S)
    /\ RespectsProgramOrder(R, S)

-----------------------------------------------------------------------------
TypeOK ==
    /\ reqQ \in [Proc -> Seq(Request)]
    /\ reqOrder \subseteq ReqId \X ReqId

OrderOK == GoodOrder(reqOrder, CurrentIds)

-----------------------------------------------------------------------------
Init ==
    /\ reqQ = [p \in Proc |-> << >>]
    /\ reqOrder = {}

IssueRequest(p) ==
    \E req \in Request :
        LET newId  == [proc |-> p, idx |-> Len(reqQ[p]) + 1]
            oldIds == CurrentIds
            newIds == oldIds \cup {newId}
            NewPairs == { <<i, newId>> : i \in oldIds }
                          \cup { <<newId, i>> : i \in oldIds }
        IN  /\ reqQ' = [reqQ EXCEPT ![p] = Append(@, req)]
            /\ \E ext \in SUBSET NewPairs :
                  LET R == reqOrder \cup ext
                  IN  /\ GoodOrder(R, newIds)
                      /\ reqOrder' = R

Next == \E p \in Proc : IssueRequest(p)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* State constraint for finite-state model checking *)
QueueConstraint == \A p \in Proc : Len(reqQ[p]) <= MaxQLen

THEOREM Spec => [](TypeOK /\ OrderOK)
=============================================================================