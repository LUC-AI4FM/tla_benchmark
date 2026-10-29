------------------------------ MODULE RequestOrdering ------------------------------
(***************************************************************************)
(* A small test model of a multiprocessor request-ordering system.         *)
(*                                                                         *)
(* Each processor keeps a queue (sequence) of pending requests. Every      *)
(* request carries an address, a value and an operation type (read or      *)
(* write). A request is identified by the pair <<processor, queue index>>. *)
(* Issuing a request appends it to the issuing processor's queue. It also  *)
(* extends a global ordering relation over request identifiers.            *)
(*                                                                         *)
(* The ordering relation must stay a strict partial order, meaning it is   *)
(* irreflexive and transitive. It must respect per-processor program       *)
(* order, and it may only grow over time.                                  *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Proc,       \* set of processors           (e.g. {p1, p2})
    Reg,        \* set of registers            (e.g. {r1})
    Adr,        \* set of addresses            (e.g. {a1})
    Val,        \* set of values               (e.g. {v1, v2})
    MaxQLen     \* bound on queue length       (e.g. 2)

ASSUME /\ Proc # {}
       /\ Reg  # {}
       /\ Adr  # {}
       /\ Val  # {}
       /\ MaxQLen \in Nat \ {0}

VARIABLES
    rq,     \* rq[p] : sequence of pending requests of processor p
    ord     \* global ordering relation over request identifiers

vars == <<rq, ord>>

-----------------------------------------------------------------------------
(* Types *)

OpType  == {"Rd", "Wr"}

Request == [adr : Adr, val : Val, op : OpType]

\* Sequences of requests with length at most MaxQLen
BSeq(S) == UNION { [1..n -> S] : n \in 0..MaxQLen }

\* Request identifiers: <<processor, queue index>>
ReqId == Proc \X (1..MaxQLen)

\* Identifiers of requests that have actually been issued
IssuedIds == { id \in ReqId : id[2] <= Len(rq[id[1]]) }

-----------------------------------------------------------------------------
(* Type invariant *)

TypeInvariant ==
    /\ rq  \in [Proc -> BSeq(Request)]
    /\ ord \subseteq (ReqId \X ReqId)

-----------------------------------------------------------------------------
(* Order properties *)

Irreflexive(R) == \A x \in ReqId : <<x, x>> \notin R

Transitive(R) ==
    \A x, y, z \in ReqId :
        (<<x, y>> \in R /\ <<y, z>> \in R) => <<x, z>> \in R

StrictPartialOrder == Irreflexive(ord) /\ Transitive(ord)

\* Earlier-issued requests of the same processor precede later ones
ProgramOrder ==
    \A p \in Proc :
        \A i, j \in 1..Len(rq[p]) :
            i < j => << <<p, i>>, <<p, j>> >> \in ord

\* The order relation only relates issued requests
OrderOverIssued == ord \subseteq (IssuedIds \X IssuedIds)

Safety == TypeInvariant /\ StrictPartialOrder /\ ProgramOrder /\ OrderOverIssued

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ rq  = [p \in Proc |-> << >>]
    /\ ord = {}

-----------------------------------------------------------------------------
(* Actions *)

(***************************************************************************)
(* Processor p issues request r. The new request gets identifier           *)
(* <<p, n>>, where n = Len(rq[p]) + 1.                                     *)
(*                                                                         *)
(* All earlier requests of p must precede it. Some chosen subset S of the  *)
(* already-issued requests of other processors may also precede it.        *)
(*                                                                         *)
(* The relation is closed transitively: every predecessor of a direct      *)
(* predecessor also precedes the new request. The new request is a sink,   *)
(* so irreflexivity and transitivity are preserved. Existing pairs are      *)
(* never removed.                                                          *)
(***************************************************************************)
Issue(p, r) ==
    LET n      == Len(rq[p]) + 1
        newId  == <<p, n>>
        own    == { <<p, i>> : i \in 1..(n - 1) }
        others == { id \in IssuedIds : id[1] # p }
    IN  /\ Len(rq[p]) < MaxQLen
        /\ \E S \subseteq others :
              LET direct == own \cup S
                  preds  == direct \cup
                            { x \in IssuedIds : \E y \in direct : <<x, y>> \in ord }
              IN  ord' = ord \cup { <<x, newId>> : x \in preds }
        /\ rq' = [rq EXCEPT ![p] = Append(@, r)]

\* All queues are full: allow stuttering so the model has no deadlock
Done ==
    /\ \A p \in Proc : Len(rq[p]) = MaxQLen
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Proc, r \in Request : Issue(p, r)
    \/ Done

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Action / temporal properties *)

\* The ordering relation never loses existing pairs
OrderMonotone == [][ord \subseteq ord']_vars

\* Queues only grow, by appending
QueueMonotone ==
    [][\A p \in Proc : SubSeq(rq'[p], 1, Len(rq[p])) = rq[p]]_vars

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => []Safety
THEOREM Spec => OrderMonotone
=============================================================================