---------------------------- MODULE RootedSpanningTree ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges, Root, Bound
VARIABLES Parent, Distance, Messages

TypeOK == 
  /\ Nodes \in Set(Nodes)
  /\ Edges \subseteq (Nodes \X Nodes)
  /\ Root \in Nodes
  /\ Bound \in Nat
  /\ Parent \in [Nodes -> Nodes]
  /\ Distance \in [Nodes -> Nat]
  /\ Messages \subseteq (Nodes \X Nodes \X Nat)

Safety == 
  /\ \A n \in Nodes : 
    /\ (n = Root) => (Parent[n] = n /\ Distance[n] = 0)
    /\ \E p \in Nodes : (p = Parent[n]) /\ ((p, n) \in Edges)
    /\ (Distance[n] < Bound) <=> (\E p \in Nodes : (p = Parent[n]) /\ ((p, n) \in Edges))
    /\ Distance[n] = IF n = Root THEN 0 ELSE (1 + Distance[Parent[n]])
  /\ \A m \in Messages : 
    /\ \E n, p \in Nodes : (m = <<n, p, Distance[n]>>) /\ ((n, p) \in Edges)

Spec == 
  /\ TypeOK
  /\ (Distance[Root] = 0)
  /\ [][
      /\ \A n \in Nodes : 
        /\ IF (n /= Root) /\ (\E m \in Messages : (m = <<Parent[n], n, Distance[Parent[n]]>>)) 
          THEN 
            /\ Parent' = [Parent EXCEPT ![n] = Parent[n]]
            /\ Distance' = [Distance EXCEPT ![n] = 1 + Distance[Parent[n]]]
            /\ Messages' = Messages \cup {<<n, p, Distance[n]>> : p \in Nodes /\ (p, n) \in Edges}
          ELSE 
            /\ Parent' = Parent
            /\ Distance' = Distance
            /\ Messages' = Messages
      /\ UNCHANGED <<Parent, Distance, Messages>>
    ]

Liveness == 
  <>[]<>(\A n \in Nodes : (\E p \in Nodes : (p = Parent[n]) /\ ((p, n) \in Edges)) /\ (Distance[n] < Bound))
=============================================================================