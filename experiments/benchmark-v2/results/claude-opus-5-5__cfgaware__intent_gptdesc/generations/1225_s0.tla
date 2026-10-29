------------------------------- MODULE RequestOrder -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Reg, Adr, Val, Proc

VARIABLES q, order

vars == <<q, order>>

-----------------------------------------------------------------------------
MaxQLen == 3

NoVal == CHOOSE v : v \notin Val

Request ==
       [op : {"Rd"}, adr : Adr, val : {NoVal}, reg : Reg]
  \cup [op : {"Wr"}, adr : Adr, val : Val,     reg : Reg]

ProcIds(p) == { <<p, i>> : i \in 1..Len(q[p]) }

ReqIds == UNION { ProcIds(p) : p \in Proc }

ProgramOrder ==
  { <<<<p, i>>, <<p, j>>>> : p \in Proc, i \in 1..Len(q[p]), j \in 1..Len(q[p]) }
    \cap { <<a, b>> \in ReqIds \X ReqIds : a[1] = b[1] /\ a[2] < b[2] }

Irreflexive(R, S) == \A x \in S : <<x, x>> \notin R

Transitive(R, S) ==
  \A x, y, z \in S : (<<x, y>> \in R /\ <<y, z>> \in R) => <<x, z>> \in R

StrictPartialOrder(R, S) == Irreflexive(R, S) /\ Transitive(R, S)

-----------------------------------------------------------------------------
TypeInvariant ==
  /\ q \in [Proc -> Seq(Request)]
  /\ order \subseteq ReqIds \X ReqIds

Init ==
  /\ q = [p \in Proc |-> << >>]
  /\ order = {}

Preds(S) == S \cup { x \in ReqIds : \E s \in S : <<x, s>> \in order }

Issue(p, req, S) ==
  LET newId == <<p, Len(q[p]) + 1>>
      before == Preds(S \cup ProcIds(p))
  IN  /\ q' = [q EXCEPT ![p] = Append(@, req)]
      /\ order' = order \cup { <<x, newId>> : x \in before }

Next ==
  \E p \in Proc, req \in Request, S \in SUBSET ReqIds :
     Issue(p, req, S)

Spec == Init /\ [][Next]_vars

Constraint == \A p \in Proc : Len(q[p]) < MaxQLen

-----------------------------------------------------------------------------
OrderInvariant ==
  /\ StrictPartialOrder(order, ReqIds)
  /\ ProgramOrder \subseteq order

QueueBound == \A p \in Proc : Len(q[p]) <= MaxQLen

NoSelfOrder == \A x \in ReqIds : <<x, x>> \notin order

Monotonic == [][order \subseteq order']_vars

THEOREM Spec => [](TypeInvariant /\ OrderInvariant /\ NoSelfOrder)
=============================================================================