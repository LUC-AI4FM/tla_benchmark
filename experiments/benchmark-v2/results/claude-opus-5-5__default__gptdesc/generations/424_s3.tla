------------------------------- MODULE RequestOrder -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,   \* set of processors
          Adr,    \* set of addresses
          Val     \* set of data values

NoVal == CHOOSE v : v \notin Val

-----------------------------------------------------------------------------
(* Typed values                                                              *)
-----------------------------------------------------------------------------

\* A request is a read of an address or a write of a value to an address.
Request == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

\* A register record holds a request and the value returned for it.
\* A free register holds no request.
Reg     == [req : Request, val : Val \cup {NoVal}]
FreeReg == [req : {"Free"}, val : {NoVal}]

\* Request identifiers: the i-th request issued by processor p is <<p, i>>.
ReqId == Proc \X (Nat \ {0})

VARIABLES reqQ,      \* reqQ[p] is the queue of register records of processor p
          reqOrder   \* a partial order on request identifiers

vars == <<reqQ, reqOrder>>

-----------------------------------------------------------------------------
(* Helpers                                                                   *)
-----------------------------------------------------------------------------

\* The identifiers of all requests issued so far.
IssuedIds == { <<p, i>> : p \in Proc, i \in 1..Len(reqQ[p]) }

\* A set of identifiers is downward closed with respect to reqOrder.
DownClosed(S) == \A x \in reqOrder : x[2] \in S => x[1] \in S

-----------------------------------------------------------------------------
(* Initial state and actions                                                 *)
-----------------------------------------------------------------------------

Init == /\ reqQ = [p \in Proc |-> << >>]
        /\ reqOrder = {}

\* Processor p issues request req: a register record is appended to its
\* queue, and the request order is extended monotonically by placing the new
\* request after a downward-closed set of previously issued requests that
\* contains all of p's earlier requests.
IssueRequest(p, req) ==
    LET newId == <<p, Len(reqQ[p]) + 1>>
        ownIds == { <<p, i>> : i \in 1..Len(reqQ[p]) }
    IN  /\ reqQ' = [reqQ EXCEPT ![p] = Append(@, [req |-> req, val |-> NoVal])]
        /\ \E Pred \in SUBSET IssuedIds :
              /\ ownIds \subseteq Pred
              /\ DownClosed(Pred)
              /\ reqOrder' = reqOrder \cup { <<r, newId>> : r \in Pred }

Next == \E p \in Proc, req \in Request : IssueRequest(p, req)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants                                                                *)
-----------------------------------------------------------------------------

TypeInvariant ==
    /\ reqQ \in [Proc -> Seq(Reg)]
    /\ reqOrder \subseteq (ReqId \X ReqId)

\* The order relates only issued requests.
OrderWellFormed ==
    \A x \in reqOrder : x[1] \in IssuedIds /\ x[2] \in IssuedIds

Transitive ==
    \A x, y \in reqOrder :
        (x[2] = y[1]) => (<<x[1], y[2]>> \in reqOrder)

Irreflexive ==
    \A x \in reqOrder : x[1] # x[2]

\* Requests of the same processor are ordered by their queue index.
ProcIndexOrder ==
    \A p \in Proc :
        \A i, j \in 1..Len(reqQ[p]) :
            (i < j) => (<< <<p, i>>, <<p, j>> >> \in reqOrder)

ReqOrderInvariant ==
    /\ OrderWellFormed
    /\ Transitive
    /\ Irreflexive
    /\ ProcIndexOrder

\* State constraint for model checking: each queue has fewer than two elements.
QConstraint == \A p \in Proc : Len(reqQ[p]) < 2

THEOREM Spec => [](TypeInvariant /\ ReqOrderInvariant)
=============================================================================