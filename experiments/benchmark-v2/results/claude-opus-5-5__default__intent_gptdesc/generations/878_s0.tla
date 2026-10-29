------------------------------ MODULE DistSpanTree ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges, Root, MaxCardinality

ASSUME /\ Root \in Nodes
       /\ \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)
       /\ MaxCardinality \in Nat
       /\ MaxCardinality >= Cardinality(Nodes)

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

\* Nodes reachable from Root within k hops
R[k \in 0..MaxCardinality] ==
    IF k = 0 THEN {Root}
             ELSE R[k-1] \cup UNION {Nbrs(x) : x \in R[k-1]}

Reachable == R[MaxCardinality]

\* Hop distance from Root (MaxCardinality for unreachable nodes)
HopDist(n) ==
    IF n \in Reachable
      THEN CHOOSE k \in 0..MaxCardinality :
               /\ n \in R[k]
               /\ \A j \in 0..(k-1) : n \notin R[j]
      ELSE MaxCardinality

VARIABLES mom, dist, msgs

vars == <<mom, dist, msgs>>

TypeOK ==
    /\ mom  \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> 0..MaxCardinality]
    /\ msgs \in [Nodes -> SUBSET (Nodes \X (0..MaxCardinality))]

Init ==
    /\ mom  = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]
    /\ msgs = [n \in Nodes |-> IF n \in Nbrs(Root) THEN {<<Root, 0>>} ELSE {}]

\* Node n receives a message m = <<sender, d>> from a neighbor
Receive(n) ==
    \E m \in msgs[n] :
        LET d == m[2] + 1 IN
        IF d < dist[n]
          THEN /\ dist' = [dist EXCEPT ![n] = d]
               /\ mom'  = [mom  EXCEPT ![n] = m[1]]
               /\ msgs' = [k \in Nodes |->
                             IF k = n THEN msgs[n] \ {m}
                             ELSE IF k \in Nbrs(n) THEN msgs[k] \cup {<<n, d>>}
                             ELSE msgs[k]]
          ELSE /\ msgs' = [msgs EXCEPT ![n] = msgs[n] \ {m}]
               /\ UNCHANGED <<mom, dist>>

Next == \E n \in Nodes : Receive(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Quiescence: no local step is enabled (no messages in transit)
Quiescent == \A n \in Nodes : msgs[n] = {}

\* Iterated parent pointer
MomPow[k \in 0..MaxCardinality] ==
    IF k = 0 THEN [n \in Nodes |-> n]
             ELSE [n \in Nodes |-> mom[MomPow[k-1][n]]]

PostCondition ==
    \A n \in Nodes :
        /\ dist[n] = HopDist(n)
        /\ IF n = Root
             THEN mom[n] = n /\ dist[n] = 0
           ELSE IF n \in Reachable
             THEN /\ mom[n] \in Nbrs(n)
                  /\ dist[mom[n]] = dist[n] - 1
                  /\ \E k \in 0..MaxCardinality : MomPow[k][n] = Root
             ELSE /\ mom[n] = n
                  /\ dist[n] = MaxCardinality

\* Safety: whenever the system has quiesced, the postcondition holds
Safety == Quiescent => PostCondition

\* Quiescence coincides with no enabled step
QuiescentIffDisabled == Quiescent <=> ~ENABLED Next

\* Liveness: the system eventually quiesces (and stays quiesced)
Termination == <>[]Quiescent

\* Liveness: eventually the postcondition holds
EventuallyCorrect == <>[](Quiescent /\ PostCondition)

THEOREM Spec => [](TypeOK /\ Safety)
THEOREM Spec => Termination /\ EventuallyCorrect
=============================================================================