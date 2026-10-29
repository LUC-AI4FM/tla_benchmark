---------------------------- MODULE RequestIssue ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processors
          Adr,       \* set of addresses
          Val        \* set of data values

NoVal == CHOOSE v : v \notin Val

-----------------------------------------------------------------------------
(* Typed request values                                                    *)
-----------------------------------------------------------------------------
Request ==
       [op : {"Rd"}, adr : Adr]
  \cup [op : {"Wr"}, adr : Adr, val : Val]

(* A free register value: a register not holding any request              *)
FreeRegister == [op : {"Free"}]

(* A register record stored in a processor queue                          *)
RegRecord == [req : Request, val : Val \cup {NoVal}]

(* Request identifiers: <<processor, index in that processor's queue>>      *)
ReqId == Proc \X (Nat \ {0})

VARIABLES queue,     \* queue[p] : sequence of register records of processor p
          reqOrder   \* global partial order over request identifiers

vars == <<queue, reqOrder>>

(* Set of identifiers of the requests issued so far                        *)
IssuedIds == { <<p, i>> : p \in Proc, i \in { j \in Nat : 1 <= j /\ j <= Len(queue[p]) } }

-----------------------------------------------------------------------------
TypeOK ==
  /\ queue \in [Proc -> Seq(RegRecord)]
  /\ reqOrder \subseteq (IssuedIds \X IssuedIds)

Init ==
  /\ queue = [p \in Proc |-> << >>]
  /\ reqOrder = {}

(* Processor p issues request req: append a register record to its queue  *)
(* and extend the global request order monotonically, placing the new     *)
(* request after every previously issued request.                         *)
IssueRequest(p, req) ==
  LET newId == <<p, Len(queue[p]) + 1>>
  IN  /\ queue' = [queue EXCEPT ![p] = Append(@, [req |-> req, val |-> NoVal])]
      /\ reqOrder' = reqOrder \cup { <<id, newId>> : id \in IssuedIds }

Next == \E p \in Proc, req \in Request : IssueRequest(p, req)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Well-formedness of the request ordering relation                        *)
-----------------------------------------------------------------------------
Transitive ==
  \A a, b, c \in IssuedIds :
     (<<a, b>> \in reqOrder /\ <<b, c>> \in reqOrder) => <<a, c>> \in reqOrder

Irreflexive ==
  \A a \in IssuedIds : <<a, a>> \notin reqOrder

ProcIndexOrder ==
  \A p \in Proc :
    \A i, j \in 1..Len(queue[p]) :
       i < j => << <<p, i>>, <<p, j>> >> \in reqOrder

ReqOrderWellFormed ==
  /\ reqOrder \subseteq (IssuedIds \X IssuedIds)
  /\ Transitive
  /\ Irreflexive
  /\ ProcIndexOrder

(* The order only grows *)
OrderMonotonic == [][reqOrder \subseteq reqOrder']_vars

-----------------------------------------------------------------------------
(* State constraint for model checking: each queue has fewer than 2 items *)
-----------------------------------------------------------------------------
QueueConstraint == \A p \in Proc : Len(queue[p]) < 2

THEOREM Spec => [](TypeOK /\ ReqOrderWellFormed)
=============================================================================