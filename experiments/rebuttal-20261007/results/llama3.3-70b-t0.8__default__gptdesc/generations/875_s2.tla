```
MODULE SpanningTree
EXTENDS Integers, TLC
CONSTANTS Nodes, Root
VARIABLES mom, dist

Init == 
  (mom = [n \in Nodes |-> IF n = Root THEN Root ELSE n])
  /\ (dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE Infinity])

Edges == {<<n, m>> : n, m \in Nodes, m \in RandomElement(SUBSET {x \in Nodes : x # n})}

TypeOK == 
  mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> Nat \cup {Infinity}]

Next == 
  \E n \in Nodes :
    /\ IF n = Root THEN FALSE
        ELSE \E m \in Nodes, d \in (0..dist[n]) :
            /\ <<n, m>> \in Edges
            /\ mom[m] # m
            /\ dist[m] < dist[n]
            /\ d < dist[n]
            /\ mom' = [mom EXCEPT ![n] = m]
            /\ dist' = [dist EXCEPT ![n] = d]
    /\ UNCHANGED <<mom, dist>> \ n

Postcondition == 
  (\A n \in Nodes : mom[n] = n \/ <<n, mom[n]]>> \in Edges)
  /\ (\A n \in Nodes : n # Root => mom[n] # n)
  /\ (\A n \in Nodes : n # Root => dist[n] # Infinity)

Safety == 
  []((TypeOK /\ Postcondition) \/ (TypeOK /\ ~Postcondition))

Liveness == 
  <>[]Postcondition

Spec == 
  Init /\ [][Next]_<<mom, dist>> /\ WF_vars(Next)
```
Note: This TLA+ specification assumes that the `RandomElement` and `SUBSET` operators are available in TLC. The `Infinity` symbol is used to represent an unbounded distance value.