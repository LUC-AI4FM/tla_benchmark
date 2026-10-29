---- MODULE SpanningTree ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, NoPrnt, root, nbrs

ProcVal == {1, 2, 3, 4}
NoPrntVal == 0
rootVal == 1
nbrsVal == {{1, 2}, {2, 3}, {3, 4}, {1, 3}}

ASSUME /\ NoPrnt \notin Proc
       /\ root \in Proc
       /\ nbrs \subseteq {e \in SUBSET Proc : Cardinality(e) = 2}

VARIABLES parent, msgs

vars == <<parent, msgs>>

Nbrs(n) == {m \in Proc : {m, n} \in nbrs}

TypeOK ==
    /\ parent \in [Proc -> Proc \cup {NoPrnt}]
    /\ msgs \in [Proc -> SUBSET Proc]

Init ==
    /\ parent = [p \in Proc |-> NoPrnt]
    /\ msgs = [p \in Proc |-> IF p \in Nbrs(root) THEN {root} ELSE {}]

Receive(p, q) ==
    /\ q \in msgs[p]
    /\ IF p # root /\ parent[p] = NoPrnt
         THEN /\ parent' = [parent EXCEPT ![p] = q]
              /\ msgs' = [r \in Proc |->
                            IF r = p THEN msgs[r] \ {q}
                            ELSE IF r \in Nbrs(p) \ {q}
                                   THEN msgs[r] \cup {p}
                                   ELSE msgs[r]]
         ELSE /\ msgs' = [msgs EXCEPT ![p] = msgs[p] \ {q}]
              /\ UNCHANGED parent

Next == \E p \in Proc : \E q \in msgs[p] : Receive(p, q)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Terminated == \A p \in Proc : msgs[p] = {}

RECURSIVE Anc(_, _)
Anc(p, n) ==
    IF n = 0 \/ parent[p] = NoPrnt
      THEN {}
      ELSE {parent[p]} \cup Anc(parent[p], n - 1)

ParentIsNbr ==
    \A p \in Proc : parent[p] # NoPrnt => parent[p] \in Nbrs(p)

RootNoParent == parent[root] = NoPrnt

NoCycle == \A p \in Proc : p \notin Anc(p, Cardinality(Proc))

ReachesRoot ==
    \A p \in Proc \ {root} :
        parent[p] # NoPrnt => root \in Anc(p, Cardinality(Proc))

IsSpanningTree ==
    /\ RootNoParent
    /\ \A p \in Proc \ {root} : parent[p] \in Nbrs(p)
    /\ \A p \in Proc \ {root} : root \in Anc(p, Cardinality(Proc))
    /\ NoCycle

Safety ==
    /\ TypeOK
    /\ ParentIsNbr
    /\ RootNoParent
    /\ NoCycle
    /\ ReachesRoot

StableCorrect == Terminated => IsSpanningTree

ParentStable ==
    [][\A p \in Proc : parent[p] # NoPrnt => parent'[p] = parent[p]]_vars

Quiescence == <>[]Terminated

Convergence == <>(Terminated /\ IsSpanningTree)

StableAfterTermination == [](Terminated => [](Terminated /\ UNCHANGED vars))

====