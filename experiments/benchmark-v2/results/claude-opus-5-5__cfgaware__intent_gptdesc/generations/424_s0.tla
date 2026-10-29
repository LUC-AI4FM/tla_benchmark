------------------------------ MODULE RequestOrder ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Reg, Adr, Val, Proc

VARIABLES queue, order

vars == <<queue, order>>

QBound == 2

RdReq == [op : {"Rd"}, adr : Adr, reg : Reg]
WrReq == [op : {"Wr"}, adr : Adr, val : Val]
Request == RdReq \cup WrReq

Id == Proc \X (1..QBound)

IssuedIds == { <<p, i>> \in Id : i \in 1..Len(queue[p]) }

-----------------------------------------------------------------------------
Init ==
    /\ queue = [p \in Proc |-> << >>]
    /\ order = {}

Preds(S) == S \cup { a \in IssuedIds : \E b \in S : <<a, b>> \in order }

Issue(p, req) ==
    /\ Len(queue[p]) < QBound
    /\ LET n     == Len(queue[p]) + 1
           newId == <<p, n>>
           own   == { <<p, j>> : j \in 1..(n - 1) }
       IN  \E S \in SUBSET IssuedIds :
              /\ queue' = [queue EXCEPT ![p] = Append(@, req)]
              /\ order' = order \cup { <<a, newId>> : a \in Preds(S \cup own) }

Next == \E p \in Proc : \E req \in Request : Issue(p, req)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
Constraint == \A p \in Proc : Len(queue[p]) <= QBound

TypeInvariant ==
    /\ queue \in [Proc -> Seq(Request)]
    /\ \A p \in Proc : Len(queue[p]) <= QBound
    /\ order \subseteq (IssuedIds \X IssuedIds)

BoundInvariant == \A p \in Proc : Len(queue[p]) <= QBound

Irreflexive == \A a \in IssuedIds : <<a, a>> \notin order

Transitive ==
    \A a, b, c \in IssuedIds :
        (<<a, b>> \in order /\ <<b, c>> \in order) => <<a, c>> \in order

StrictPartialOrder == Irreflexive /\ Transitive

ProgramOrder ==
    \A p \in Proc : \A i, j \in 1..Len(queue[p]) :
        i < j => << <<p, i>>, <<p, j>> >> \in order

Safety == TypeInvariant /\ BoundInvariant /\ StrictPartialOrder /\ ProgramOrder

OrderMonotonic == [][order \subseteq order']_vars

=============================================================================