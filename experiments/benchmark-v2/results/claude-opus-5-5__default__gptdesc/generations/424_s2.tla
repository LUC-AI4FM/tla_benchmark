---------------------------- MODULE RequestOrder ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,   \* set of processors
          Adr,    \* set of addresses
          Val     \* set of data values

VARIABLES reqQ,     \* reqQ[p] : the request queue of processor p
          reqOrder  \* global partial order over request identifiers

vars == <<reqQ, reqOrder>>

-----------------------------------------------------------------------------
(* Typed values *)

NoVal == CHOOSE v : v \notin Val

Request == [op : {"Rd"}, adr : Adr]
             \cup [op : {"Wr"}, adr : Adr, val : Val]

\* A register record that has been issued but not yet served.
FreeRegValue == [req : Request, val : {NoVal}, status : {"Free"}]

\* Request identifiers: processor and position in its queue.
ReqId == Proc \X (Nat \ {0})

\* The identifiers of all requests currently in the queues q.
IdsOf(q) == {<<p, i>> : p \in Proc, i \in 1..Len(q[p])}

-----------------------------------------------------------------------------
(* Well-formedness of an ordering relation R relative to queues q *)

Transitive(R) ==
  \A a, b, c \in IdsOf(reqQ) \cup {x[1] : x \in R} \cup {x[2] : x \in R} :
      (<<a, b>> \in R /\ <<b, c>> \in R) => <<a, c>> \in R

Irreflexive(R) == \A x \in R : x[1] # x[2]

ProcIndexOrder(R, q) ==
  \A p \in Proc : \A i, j \in 1..Len(q[p]) :
      i < j => <<<<p, i>>, <<p, j>>>> \in R

IsOrder(R, q) ==
  /\ R \subseteq IdsOf(q) \X IdsOf(q)
  /\ \A a, b, c \in IdsOf(q) :
        (<<a, b>> \in R /\ <<b, c>> \in R) => <<a, c>> \in R
  /\ Irreflexive(R)
  /\ ProcIndexOrder(R, q)

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
  /\ reqQ = [p \in Proc |-> << >>]
  /\ reqOrder = {}

(* Processor p issues request req: it appends a free register record to its
   queue and the global request order is extended monotonically. *)
IssueRequest(p, req) ==
  /\ reqQ' = [reqQ EXCEPT ![p] =
                 Append(@, [req |-> req, val |-> NoVal, status |-> "Free"])]
  /\ \E R \in SUBSET (IdsOf(reqQ') \X IdsOf(reqQ')) :
        /\ reqOrder \subseteq R
        /\ IsOrder(R, reqQ')
        /\ reqOrder' = R

Next == \E p \in Proc, req \in Request : IssueRequest(p, req)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
  /\ reqQ \in [Proc -> Seq(FreeRegValue)]
  /\ \A x \in reqOrder : x \in ReqId \X ReqId

ReqOrderWellFormed ==
  reqOrder \subseteq IdsOf(reqQ) \X IdsOf(reqQ)

ReqOrderTransitive ==
  \A a, b, c \in IdsOf(reqQ) :
     (<<a, b>> \in reqOrder /\ <<b, c>> \in reqOrder) => <<a, c>> \in reqOrder

ReqOrderIrreflexive == Irreflexive(reqOrder)

ReqOrderProcIndex == ProcIndexOrder(reqOrder, reqQ)

ReqOrderInv ==
  /\ ReqOrderWellFormed
  /\ ReqOrderTransitive
  /\ ReqOrderIrreflexive
  /\ ReqOrderProcIndex

(* State constraint for model checking: each queue has fewer than 2 elements *)
QueueConstraint == \A p \in Proc : Len(reqQ[p]) < 2

THEOREM Spec => [](TypeOK /\ ReqOrderInv)
=============================================================================