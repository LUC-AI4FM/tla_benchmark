------------------------------ MODULE SpanningTree ------------------------------
EXTENDS Naturals

CONSTANTS NODES, EDGES, ROOT, BOUND

ASSUME
  /\ ROOT \in NODES
  /\ BOUND >= 1
  /\ NoSelfLoops == ~(\E i \in NODES : (i,i) \in EDGES)
  /\ UndirectedEdges == (\A i,j \in NODES : ((i,j) \in EDGES) <=> ((j,i) \in EDGES))

Neighbors(n) == { m \in NODES : (n,m) \in EDGES }

VARIABLES parent, dist, inbox

Init ==
  /\ parent = [i \in NODES |-> i]
  /\ dist   = [i \in NODES |-> IF i = ROOT THEN 0 ELSE BOUND]
  /\ inbox  = [i \in NODES |-> {}]

Receive ==
  LET
    i == CHOOSE j \in NODES : inbox[j] # {}
    m == CHOOSE msg \in inbox[i] : TRUE
    src == [m]_1
    dsrc == [m]_2
    newDist == dsrc + 1
    inbox0 == [ inbox EXCEPT ![i] = inbox[i] \ {m} ]
  IN
    /\ IF newDist < dist[i]
       THEN
         /\ parent' = [ parent EXCEPT ![i] = src ]
         /\ dist'   = [ dist   EXCEPT ![i] = newDist ]
         /\ inbox'  = [ k \in NODES |-> IF k \in Neighbors(i) THEN inbox0[k] \cup { <<i, newDist>> } ELSE inbox0[k] ]
       ELSE
         /\ parent' = parent
         /\ dist'   = dist
         /\ inbox'  = inbox0

Next == Receive

Safety ==
  /\ parent[ROOT] = ROOT
  /\ \A i \in NODES :
        (dist[i] = 0 => i = ROOT) /\
        (dist[i] > 0 /\ dist[i] < BOUND =>
           parent[i] \in Neighbors(i) /\ dist[parent[i]] = dist[i]-1) /\
        (dist[i] = BOUND => parent[i] = i)

Quiescent == \A i \in NODES : inbox[i] = {}

Liveness ==
  []<>(Quiescent /\ Safety)

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Receive)
--------------------------------------------------------------------------