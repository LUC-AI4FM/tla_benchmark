---------------------------- MODULE RequestOrder ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Reg, Adr, Val, Proc

VARIABLES reqQ, reqOrder

vars == <<reqQ, reqOrder>>

-----------------------------------------------------------------------------
(* Typed request values *)
Request ==
    [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

(* Value held by a free (unused) register *)
FreeRegValue == [op : {"Free"}]

(* A register record placed in a processor's queue *)
RegRecord == [req : Request, reg : Reg]

(* Request identifiers: processor and index into its queue *)
ReqId == Proc \X (Nat \ {0})

(* Identifiers of all requests currently issued *)
IssuedIds == { <<p, i>> : p \in Proc, i \in 1..Len(reqQ[p]) }

-----------------------------------------------------------------------------
TypeInvariant ==
    /\ reqQ \in [Proc -> Seq(RegRecord)]
    /\ reqOrder \subseteq (ReqId \X ReqId)

(* Well-formedness of the request ordering relation *)
Transitive ==
    \A a, b, c \in IssuedIds :
        (<<a, b>> \in reqOrder /\ <<b, c>> \in reqOrder) => <<a, c>> \in reqOrder

Irreflexive ==
    \A a \in IssuedIds : <<a, a>> \notin reqOrder

ProcIndexOrder ==
    \A p \in Proc :
        \A i, j \in 1..Len(reqQ[p]) :
            i < j => << <<p, i>>, <<p, j>> >> \in reqOrder

OrderOverIssued ==
    \A e \in reqOrder : e[1] \in IssuedIds /\ e[2] \in IssuedIds

WellFormedOrder ==
    /\ OrderOverIssued
    /\ Transitive
    /\ Irreflexive
    /\ ProcIndexOrder

-----------------------------------------------------------------------------
Init ==
    /\ reqQ = [p \in Proc |-> << >>]
    /\ reqOrder = {}

(* Processor p issues request req using register r. The new request is
   ordered after every previously issued request, so the order is
   extended monotonically. *)
IssueRequest(p, req, r) ==
    LET newId == <<p, Len(reqQ[p]) + 1>>
    IN  /\ reqQ' = [reqQ EXCEPT ![p] = Append(@, [req |-> req, reg |-> r])]
        /\ reqOrder' = reqOrder \cup { <<id, newId>> : id \in IssuedIds }

Next ==
    \E p \in Proc, req \in Request, r \in Reg : IssueRequest(p, req, r)

Spec == Init /\ [][Next]_vars

(* State constraint bounding each processor queue *)
Constraint == \A p \in Proc : Len(reqQ[p]) < 2

THEOREM Spec => [](TypeInvariant /\ WellFormedOrder)
=============================================================================