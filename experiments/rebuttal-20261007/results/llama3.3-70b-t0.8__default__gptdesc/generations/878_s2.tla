```tla
MODULE RootedSpanningTree

EXTENDS Integers, FiniteSets

CONSTANTS Nodes, root, MaxCardinality

VARIABLES mom, dist

Init ==
  /\ mom = [n \in Nodes |-> n]
  /\ dist = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxCardinality]

Next ==
  /\ CHOOSE n \in Nodes : 
    /\ dist[n] # 0
    /\ CHOOSE neighbor \in Nodes :
      /\ {n, neighbor} \subseteq Nodes
      /\ mom[neighbor] = neighbor
      /\ dist[neighbor] < dist[n]
  /\ LET d == CHOOSE v \in (dist[neighbor])..(dist[n] - 1) : TRUE
  IN
    /\ mom' = [mom EXCEPT ![n] = neighbor]
    /\ dist' = [dist EXCEPT ![n] = d]

Spec ==
  /\ Init
  /\ [][Next]_<<mom, dist>>
  /\ WF_<<mom, dist>>(Next)

TerminationImpliesPostcondition == 
  []<>(\A n \in Nodes : mom[n] = root)

EventualTermination == 
  <>[]~(CHOOSE n \in Nodes : dist[n] # 0)

EveryNodeEventuallyHasRootAsParent == 
  [](CHOOSE n \in Nodes : mom[n] = root)

THEOREM Spec => []TerminationImpliesPostcondition
THEOREM Spec => EventualTermination
THEOREM Spec => EveryNodeEventuallyHasRootAsParent

```
Note that I've left out any explanation of the TLA+ specification, as per your request. Let me know if you have any further questions or need additional clarification!