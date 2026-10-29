---------------------------- MODULE RequestQueues ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,   \* set of processors
          Adr,    \* set of memory addresses
          Val     \* set of data values

ASSUME Proc # {} /\ Adr # {} /\ Val # {}

VARIABLES queue,     \* queue[p] : sequence of register records issued by p
          reqOrder   \* global partial order over request identifiers

vars == <<queue, reqOrder>>

-----------------------------------------------------------------------------
(* Typed values *)

NoVal == CHOOSE v : v \notin Val
NoAdr == CHOOSE a : a \notin Adr

Request ==
     [op : {"Rd"}, adr : Adr]
  \cup [op : {"Wr"}, adr : Adr, val : Val]

FreeRequest == [op |-> "Free", adr |-> NoAdr]

\* A register holds a request and the (possibly not-yet-known) result value
RegRecord == [req : Request, val : Val \cup {NoVal}]

FreeRegValue == [req |-> FreeRequest, val |-> NoVal]

\* Request identifiers: <<p, i>> is the i-th request issued by processor p
IdsOf(q) == { <<p, i>> : p \in Proc, i \in 1..Len(q[p]) }
ReqIds   == IdsOf(queue)

-----------------------------------------------------------------------------
(* Invariants *)

TypeInvariant ==
  /\ queue \in [Proc -> Seq(RegRecord)]
  /\ \A pr \in reqOrder :
        /\ pr \in ReqIds \X ReqIds

Irreflexive ==
  \A id \in ReqIds : <<id, id>> \notin reqOrder

Transitive ==
  \A a, b, c \in ReqIds :
     (<<a, b>> \in reqOrder /\ <<b, c>> \in reqOrder) => <<a, c>> \in reqOrder

ProcIndexOrder ==
  \A p \in Proc : \A i, j \in 1..Len(queue[p]) :
     i < j => << <<p, i>>, <<p, j>> >> \in reqOrder

WellFormedReqOrder ==
  /\ reqOrder \subseteq ReqIds \X ReqIds
  /\ Irreflexive
  /\ Transitive
  /\ ProcIndexOrder

\* State constraint bounding the model
QueueConstraint == \A p \in Proc : Len(queue[p]) < 2

-----------------------------------------------------------------------------
(* Initial state and actions *)

Init ==
  /\ queue    = [p \in Proc |-> << >>]
  /\ reqOrder = {}

\* Processor p issues request r: append a register record to its queue and
\* extend the global order monotonically, placing the new request after
\* every previously issued request.
IssueRequest(p, r) ==
  LET newId == <<p, Len(queue[p]) + 1>>
  IN  /\ queue'    = [queue EXCEPT ![p] = Append(@, [req |-> r, val |-> NoVal])]
      /\ reqOrder' = reqOrder \cup { <<id, newId>> : id \in ReqIds }

Next == \E p \in Proc, r \in Request : IssueRequest(p, r)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Properties *)

\* The request order only ever grows
MonotoneOrder == [][reqOrder \subseteq reqOrder']_vars

THEOREM Spec => [](TypeInvariant /\ WellFormedReqOrder)
=============================================================================