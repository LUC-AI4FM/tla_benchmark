------------------------------- MODULE RequestOrder -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Reg, Adr, Val, Proc

MaxQLen == 2

OpType == {"Rd", "Wr"}

Request == [reg : Reg, adr : Adr, val : Val, op : OpType]

ReqId == Proc \X (1..MaxQLen)

VARIABLES reqQ, ord

vars == <<reqQ, ord>>

(* Identifiers of all requests currently in the queues *)
Ids == { <<q, i>> : q \in Proc, i \in 1..Len(reqQ[q]) } \cap ReqId

(* Strict partial order properties *)
Irreflexive(R) == \A x \in ReqId : <<x, x>> \notin R

Transitive(R) ==
  \A x, y, z \in ReqId :
     (<<x, y>> \in R /\ <<y, z>> \in R) => <<x, z>> \in R

ProgramOrder(R) ==
  \A q \in Proc : \A i, j \in 1..Len(reqQ[q]) :
     (i < j) => <<<<q, i>>, <<q, j>>>> \in R

TypeInvariant ==
  /\ reqQ \in [Proc -> Seq(Request)]
  /\ \A q \in Proc : Len(reqQ[q]) <= MaxQLen
  /\ ord \subseteq (ReqId \X ReqId)

OrderInvariant ==
  /\ Irreflexive(ord)
  /\ Transitive(ord)
  /\ ProgramOrder(ord)

Init ==
  /\ reqQ = [q \in Proc |-> << >>]
  /\ ord = {}

(* Processor p issues a new request r. The new request is placed after all  *)
(* earlier requests of p and after an arbitrary set S of existing requests,  *)
(* together with everything already ordered before those. Because the new  *)
(* request is a sink, the extended relation stays a strict partial order.   *)
Issue(p, r, S) ==
  LET n      == Len(reqQ[p]) + 1
      newId  == <<p, n>>
      Direct == S \cup { <<p, i>> : i \in 1..Len(reqQ[p]) }
      Pre    == Direct \cup { x \in Ids : \E y \in Direct : <<x, y>> \in ord }
  IN  /\ Len(reqQ[p]) < MaxQLen
      /\ reqQ' = [reqQ EXCEPT ![p] = Append(@, r)]
      /\ ord'  = ord \cup { <<x, newId>> : x \in Pre }

Next ==
  \E p \in Proc :
    \E r \in Request :
      \E S \in SUBSET Ids :
        Issue(p, r, S)

Spec == Init /\ [][Next]_vars

(* Order pairs are never lost *)
OrderGrows == [][ord \subseteq ord']_vars

Constraint == \A q \in Proc : Len(reqQ[q]) <= MaxQLen

===================================================================================