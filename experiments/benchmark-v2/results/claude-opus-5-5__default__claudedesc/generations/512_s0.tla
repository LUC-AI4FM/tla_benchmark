------------------------------ MODULE Session10set ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, root, MaxNodes

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

RECURSIVE Reach(_)
Reach(k) == IF k = 0
              THEN {root}
              ELSE Reach(k-1) \cup
                   {n \in Nodes : \E m \in Reach(k-1) : {m, n} \in Edges}

ASSUME /\ \A e \in Edges : e \subseteq Nodes /\ Cardinality(e) = 2
       /\ root \in Nodes
       /\ MaxNodes \in Nat
       /\ Reach(MaxNodes) = Nodes

Chans == {<<m, n>> \in Nodes \X Nodes : {m, n} \in Edges}

VARIABLES msgs, depth, parent

vars == <<msgs, depth, parent>>

TypeOK ==
    /\ msgs \in [Chans -> SUBSET (0..MaxNodes)]
    /\ depth \in [Nodes -> 0..MaxNodes]
    /\ parent \in [Nodes -> Nodes]

Init ==
    /\ depth = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes]
    /\ parent = [n \in Nodes |-> n]
    /\ msgs = [c \in Chans |-> IF c[1] = root THEN {0} ELSE {}]

Proc(n) ==
    \E m \in Nbrs(n) :
      \E d \in msgs[<<m, n>>] :
        IF d + 1 < depth[n]
          THEN /\ depth' = [depth EXCEPT ![n] = d + 1]
               /\ parent' = [parent EXCEPT ![n] = m]
               /\ msgs' = [c \in Chans |->
                             IF c = <<m, n>>
                               THEN msgs[c] \ {d}
                             ELSE IF c[1] = n /\ c[2] # m
                               THEN msgs[c] \cup {d + 1}
                             ELSE msgs[c]]
          ELSE /\ msgs' = [msgs EXCEPT ![<<m, n>>] = @ \ {d}]
               /\ UNCHANGED <<depth, parent>>

Next == \E n \in Nodes : Proc(n)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A n \in Nodes : WF_vars(Proc(n))

=============================================================================