---------------------------- MODULE RequestOrder ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Reg, Adr, Val, Proc

VARIABLES reqQ, reqOrder

vars == <<reqQ, reqOrder>>

Ops == {"Rd", "Wr"}

Request == [adr : Adr, val : Val, op : Ops]

ReqId == Proc \X Nat

IdsOf(q) == { <<p, i>> : p \in Proc, i \in {} } \cup
            UNION { { <<p, i>> : i \in 1..Len(q[p]) } : p \in Proc }

Irreflexive(R, S) == \A x \in S : <<x, x>> \notin R

Transitive(R, S) ==
    \A x, y, z \in S :
        (<<x, y>> \in R /\ <<y, z>> \in R) => <<x, z>> \in R

IsStrictPartialOrder(R, S) == Irreflexive(R, S) /\ Transitive(R, S)

RespectsProgramOrder(R, q) ==
    \A p \in Proc :
        \A i, j \in 1..Len(q[p]) :
            i < j => <<<<p, i>>, <<p, j>>>> \in R

TypeInvariant ==
    /\ reqQ \in [Proc -> Seq(Request)]
    /\ reqOrder \subseteq (ReqId \X ReqId)

Init ==
    /\ reqQ = [p \in Proc |-> << >>]
    /\ reqOrder = {}

IssueRequest(p, a, v, op) ==
    LET newQ   == [reqQ EXCEPT ![p] = Append(@, [adr |-> a, val |-> v, op |-> op])]
        newId  == <<p, Len(reqQ[p]) + 1>>
        oldIds == IdsOf(reqQ)
        allIds == IdsOf(newQ)
        Cands  == { <<i, newId>> : i \in oldIds } \cup { <<newId, i>> : i \in oldIds }
    IN  /\ reqQ' = newQ
        /\ \E N \in SUBSET Cands :
              LET R == reqOrder \cup N
              IN  /\ IsStrictPartialOrder(R, allIds)
                  /\ RespectsProgramOrder(R, newQ)
                  /\ reqOrder' = R

Next ==
    \E p \in Proc, a \in Adr, v \in Val, op \in Ops :
        IssueRequest(p, a, v, op)

Spec == Init /\ [][Next]_vars

Constraint == \A p \in Proc : Len(reqQ[p]) <= 2

=============================================================================