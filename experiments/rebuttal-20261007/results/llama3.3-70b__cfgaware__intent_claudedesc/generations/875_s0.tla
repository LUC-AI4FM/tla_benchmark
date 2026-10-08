---------------------------- MODULE DistributedSpanningTree ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Nodes, Root
VARIABLE Distance, Parent

TypeOK == /\ Nodes \subseteq Nat
          /\ Root \in Nodes
          /\ Distance \in [Nodes -> Nat]
          /\ Parent \in [Nodes -> Nodes]

Init == /\ TypeOK
         /\ Distance = [n \in Nodes |-> IF n = Root THEN 0 ELSE Cardinality(Nodes)]
         /\ Parent = [n \in Nodes |-> n]

Next(n) == /\ n \in Nodes
            /\ \E m \in Nodes :
                /\ {m, n} \subseteq Nodes
                /\ m /= n
                /\ Distance[m] < Distance[n] - 1
                /\ Distance[n] > Distance[m] + 1
                /\ Distance' = [Distance EXCEPT ![n] = Distance[m] + 1]
                /\ Parent' = [Parent EXCEPT ![n] = m]
            \/ /\ n \in Nodes
               /\ \A m \in Nodes :
                   /\ {m, n} \subseteq Nodes
                   /\ m /= n
                   /\ ~(Distance[m] < Distance[n] - 1
                         /\ Distance[n] > Distance[m] + 1)
               /\ Distance' = Distance
               /\ Parent' = Parent

Next == \E n \in Nodes : Next(n)

Spec == Init /\ [][Next]_<<Distance, Parent>>

Liveness == <>[](~\E n \in Nodes : \E m \in Nodes :
                   {m, n} \subseteq Nodes
                   /\ m /= n
                   /\ Distance[m] < Distance[n] - 1
                   /\ Distance[n] > Distance[m] + 1))

Safety == [](\A n \in Nodes : (\E m \in Nodes :
                                {m, n} \subseteq Nodes
                                /\ m /= n
                                /\ Distance[m] < Distance[n] - 1
                                /\ Distance[n] > Distance[m] + 1)
                            \/ (Distance[n] = Cardinality(Nodes)
                                /\ ~\E m \in Nodes :
                                    {m, n} \subseteq Nodes
                                    /\ m /= n
                                    /\ Distance[m] < Distance[n])))

=============================================================================