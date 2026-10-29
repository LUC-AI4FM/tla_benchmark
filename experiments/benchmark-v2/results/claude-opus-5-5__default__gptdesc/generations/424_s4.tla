---------------------------- MODULE RequestOrder ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processors
          Adr,       \* set of memory addresses
          Val,       \* set of data values
          NoVal      \* value of a free (not yet answered) register

ASSUME NoVal \notin Val

VARIABLES reqQ,      \* reqQ[p] : sequence of register records issued by p
          reqOrder   \* global partial order over request identifiers

vars == <<reqQ, reqOrder>>

-----------------------------------------------------------------------------
(* Typed request values *)
Request == [type : {"Rd"}, adr : Adr]
             \cup [type : {"Wr"}, adr : Adr, val : Val]

(* Free-register values: a register holding a request with no answer yet *)
FreeRegValue == [req : Request, val : {NoVal}]

(* General register values *)
RegValue == [req : Request, val : Val \cup {NoVal}]

(* Request identifiers: <<processor, index in its queue>> *)
ReqId == Proc \X (Nat \ {0})

(* Set of identifiers of all requests currently issued *)
IssuedIds == { <<p, i>> : p \in Proc, i \in 1..Len(reqQ[p]) }

-----------------------------------------------------------------------------
TypeOK ==
  /\ reqQ \in [Proc -> Seq(RegValue)]
  /\ reqOrder \subseteq (ReqId \X ReqId)

(* The ordering relation only relates issued requests *)
ReqOrderWellFormed ==
  \A pr \in reqOrder : pr[1] \in IssuedIds /\ pr[2] \in IssuedIds

ReqOrderTransitive ==
  \A a, b, c \in IssuedIds :
     (<<a, b>> \in reqOrder /\ <<b, c>> \in reqOrder) => <<a, c>> \in reqOrder

ReqOrderIrreflexive ==
  \A a \in IssuedIds : <<a, a>> \notin reqOrder

(* Requests of a single processor are ordered by their queue index *)
ReqOrderPerProc ==
  \A p \in Proc :
    \A i, j \in 1..Len(reqQ[p]) :
       i < j => << <<p, i>>, <<p, j>> >> \in reqOrder

ReqOrderOK ==
  /\ ReqOrderWellFormed
  /\ ReqOrderTransitive
  /\ ReqOrderIrreflexive
  /\ ReqOrderPerProc

-----------------------------------------------------------------------------
Init ==
  /\ reqQ = [p \in Proc |-> << >>]
  /\ reqOrder = {}

(* A set of issued ids that is closed downward under reqOrder *)
DownClosed(S) ==
  \A a \in S : \A b \in IssuedIds : <<b, a>> \in reqOrder => b \in S

(* Processor p issues request req.  The new request is placed after a
   downward-closed set of existing requests that contains all of p's
   earlier requests, so the order is extended monotonically. *)
IssueRequest(p, req) ==
  LET newId == <<p, Len(reqQ[p]) + 1>>
      own   == { <<p, i>> : i \in 1..Len(reqQ[p]) }
  IN  \E S \in SUBSET IssuedIds :
        /\ own \subseteq S
        /\ DownClosed(S)
        /\ reqQ' = [reqQ EXCEPT ![p] = Append(@, [req |-> req, val |-> NoVal])]
        /\ reqOrder' = reqOrder \cup { <<a, newId>> : a \in S }

Next == \E p \in Proc, req \in Request : IssueRequest(p, req)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* State constraint for model checking *)
QueueConstraint == \A p \in Proc : Len(reqQ[p]) < 2

THEOREM Spec => [](TypeOK /\ ReqOrderOK)
=============================================================================