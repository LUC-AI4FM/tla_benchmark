---------------------------- MODULE MCSession10 ----------------------------
(***************************************************************************)
(* Model-checking module for the Session10 system, made self-contained:   *)
(* the Session10 system is included inline.                                *)
(*                                                                         *)
(* A rooted, undirected graph is explored by distance-vector messages.     *)
(* Each node keeps a depth, which is its current distance estimate to the  *)
(* Root, and a parent pointer. Each node also has a FIFO message queue.    *)
(* When a node learns of a shorter path, it updates its depth and parent   *)
(* and notifies all of its neighbours.                                     *)
(*                                                                         *)
(* The checked properties are:                                             *)
(*   - Termination: eventually all queues are empty.                       *)
(*   - TypeOK: type correctness of the variables and message contents.     *)
(*   - Correctness: termination implies the postcondition. The             *)
(*     postcondition says that the path built by following parent         *)
(*     pointers has the same length as the graph distance to the Root.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Edges, Root

ASSUME RootOK  == Root \in Nodes
ASSUME EdgesOK == \A e \in Edges : e \subseteq Nodes /\ Cardinality(e) = 2

N == Cardinality(Nodes)          \* used as "infinity" (no path known)

Nbrs(n) == {m \in Nodes : {n, m} \in Edges}

Msg == [from : Nodes, d : 0..N]

VARIABLES depth, parent, queue

vars == <<depth, parent, queue>>

-----------------------------------------------------------------------------
(* The Session10 system *)

Init ==
  /\ depth  = [n \in Nodes |-> IF n = Root THEN 0 ELSE N]
  /\ parent = [n \in Nodes |-> n]
  /\ queue  = [n \in Nodes |->
                 IF n \in Nbrs(Root) THEN << [from |-> Root, d |-> 0] >>
                                     ELSE << >>]

Receive(n) ==
  /\ queue[n] # << >>
  /\ LET m        == Head(queue[n])
         improved == m.d + 1 < depth[n]
         out      == [from |-> n, d |-> m.d + 1]
     IN  /\ depth'  = IF improved THEN [depth  EXCEPT ![n] = m.d + 1]  ELSE depth
         /\ parent' = IF improved THEN [parent EXCEPT ![n] = m.from]   ELSE parent
         /\ queue'  = [k \in Nodes |->
                         IF k = n THEN Tail(queue[n])
                         ELSE IF improved /\ k \in Nbrs(n)
                              THEN Append(queue[k], out)
                              ELSE queue[k]]

Terminated == \A n \in Nodes : queue[n] = << >>

Done == Terminated /\ UNCHANGED vars

Next == (\E n \in Nodes : Receive(n)) \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(\E n \in Nodes : Receive(n))

-----------------------------------------------------------------------------
(* Recursive definitions: graph distance and parent paths *)

RECURSIVE Within(_)
\* Within(k) is the set of nodes that are at most k hops from the Root.
Within(k) ==
  IF k = 0 THEN {Root}
  ELSE Within(k - 1) \cup
       {m \in Nodes : \E x \in Within(k - 1) : {x, m} \in Edges}

\* Distance(n) is the graph distance from n to the Root.
\* It is N when n cannot reach the Root.
Distance(n) ==
  IF n \in Within(N)
  THEN CHOOSE k \in 0..N : /\ n \in Within(k)
                           /\ \A j \in 0..N : n \in Within(j) => k <= j
  ELSE N

RECURSIVE PathLen(_, _)
\* PathLen(n, fuel) is the length of the path from n to the Root found by
\* following parent pointers. It is N when no such path exists.
PathLen(n, fuel) ==
  IF n = Root THEN 0
  ELSE IF fuel = 0 \/ parent[n] = n THEN N
  ELSE LET r == PathLen(parent[n], fuel - 1)
       IN  IF r >= N THEN N ELSE r + 1

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
  /\ depth  \in [Nodes -> 0..N]
  /\ parent \in [Nodes -> Nodes]
  /\ queue  \in [Nodes -> Seq(Msg)]
  /\ \A n \in Nodes : \A i \in 1..Len(queue[n]) :
        /\ queue[n][i].from \in Nbrs(n)
        /\ queue[n][i].d \in 0..(N - 1)

Postcondition ==
  \A n \in Nodes :
     /\ depth[n] = Distance(n)
     /\ Distance(n) < N => PathLen(n, N) = Distance(n)
     /\ (n # Root /\ Distance(n) < N) => parent[n] \in Nbrs(n)

Termination == <>Terminated

Correctness == Terminated => Postcondition

THEOREM Spec => []TypeOK
THEOREM Spec => []Correctness
THEOREM Spec => Termination
=============================================================================