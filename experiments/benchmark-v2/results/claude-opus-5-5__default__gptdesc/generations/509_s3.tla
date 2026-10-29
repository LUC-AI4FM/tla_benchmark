------------------------------- MODULE MCSession10 -------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Edges, Root

ASSUME RootInNodes == Root \in Nodes
ASSUME EdgesWellFormed == Edges \subseteq (Nodes \X Nodes)

NoParent == CHOOSE x : x \notin Nodes

Inf == Cardinality(Nodes)

Nbrs(n) == { m \in Nodes : <<n, m>> \in Edges \/ <<m, n>> \in Edges }

Msg == [from : Nodes, d : 0..Inf]

VARIABLES depth, parent, queues

vars == << depth, parent, queues >>

-----------------------------------------------------------------------------
(* The underlying system (Session10): distributed BFS spanning-tree build *)

Init ==
  /\ depth  = [n \in Nodes |-> IF n = Root THEN 0 ELSE Inf]
  /\ parent = [n \in Nodes |-> NoParent]
  /\ queues = [n \in Nodes |->
                 IF n \in Nbrs(Root)
                   THEN << [from |-> Root, d |-> 0] >>
                   ELSE << >>]

Receive(n) ==
  /\ queues[n] # << >>
  /\ LET msg == Head(queues[n])
         nd  == msg.d + 1
     IN  IF nd < depth[n]
           THEN /\ depth'  = [depth  EXCEPT ![n] = nd]
                /\ parent' = [parent EXCEPT ![n] = msg.from]
                /\ queues' = [m \in Nodes |->
                                IF m = n
                                  THEN IF n \in Nbrs(n)
                                         THEN Append(Tail(queues[n]), [from |-> n, d |-> nd])
                                         ELSE Tail(queues[n])
                                  ELSE IF m \in Nbrs(n)
                                         THEN Append(queues[m], [from |-> n, d |-> nd])
                                         ELSE queues[m]]
           ELSE /\ queues' = [queues EXCEPT ![n] = Tail(queues[n])]
                /\ UNCHANGED << depth, parent >>

Termination == \A n \in Nodes : queues[n] = << >>

Terminated == Termination /\ UNCHANGED vars

Next == (\E n \in Nodes : Receive(n)) \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(\E n \in Nodes : Receive(n))

-----------------------------------------------------------------------------
(* Model-checking wrapper properties *)

TypeOK ==
  /\ depth  \in [Nodes -> 0..Inf]
  /\ parent \in [Nodes -> Nodes \cup {NoParent}]
  /\ queues \in [Nodes -> Seq(Msg)]
  /\ \A n \in Nodes : \A i \in 1..Len(queues[n]) :
        /\ queues[n][i] \in Msg
        /\ queues[n][i].from \in Nbrs(n)

(* Nodes within k hops of Root *)
RECURSIVE Within(_)
Within(k) ==
  IF k = 0 THEN {Root}
  ELSE LET prev == Within(k - 1)
       IN  prev \cup { n \in Nodes : \E m \in prev : n \in Nbrs(m) }

Reachable(n) == \E k \in 0..Inf : n \in Within(k)

Distance(n) ==
  IF Reachable(n)
    THEN CHOOSE k \in 0..Inf :
            /\ n \in Within(k)
            /\ \A j \in 0..Inf : j < k => n \notin Within(j)
    ELSE Inf

(* Length of the path obtained by following parent pointers to Root,
   bounded by fuel to guarantee well-founded recursion *)
RECURSIVE PathLen(_, _)
PathLen(n, fuel) ==
  IF n = Root THEN 0
  ELSE IF fuel = 0 \/ parent[n] = NoParent THEN Inf
  ELSE LET rest == PathLen(parent[n], fuel - 1)
       IN  IF rest >= Inf THEN Inf ELSE 1 + rest

ParentPathLen(n) == PathLen(n, Inf)

(* Each parent pointer is an edge of the graph *)
ParentIsEdge ==
  \A n \in Nodes : parent[n] # NoParent => parent[n] \in Nbrs(n)

Postcondition ==
  /\ ParentIsEdge
  /\ \A n \in Nodes :
       IF Reachable(n)
         THEN /\ depth[n] = Distance(n)
              /\ ParentPathLen(n) = Distance(n)
         ELSE /\ depth[n] = Inf
              /\ parent[n] = NoParent

Correctness == Termination => Postcondition

EventuallyTerminates == <>Termination

CorrectnessAlways == [](Termination => Postcondition)

THEOREM Spec => []TypeOK
THEOREM Spec => []Correctness
THEOREM Spec => EventuallyTerminates
=============================================================================