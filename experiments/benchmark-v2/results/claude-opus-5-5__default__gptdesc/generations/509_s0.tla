---------------------------- MODULE MCSession10 ----------------------------
(***************************************************************************)
(* Model-checking module for the Session10 system: an asynchronous         *)
(* distributed construction of a BFS spanning tree rooted at Root.  Each   *)
(* node keeps a depth estimate, a parent pointer and a FIFO message queue. *)
(* Once all queues are empty, the parent relation defines paths to the     *)
(* root whose lengths equal the graph distance to the root.                *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Node,     \* the set of nodes
          Edges,    \* set of undirected edges, each a 2-element set of nodes
          Root      \* the distinguished root node

ASSUME /\ Root \in Node
       /\ Edges \subseteq SUBSET Node
       /\ \A e \in Edges : Cardinality(e) = 2

VARIABLES depth, parent, msgs

vars == <<depth, parent, msgs>>

N == Cardinality(Node)
Infinity == N + 1

Nbrs(n) == {m \in Node : {n, m} \in Edges}

Msg == [src : Node, d : 0..Infinity]

(***************************************************************************)
(* The system (Session10)                                                  *)
(***************************************************************************)
Init ==
  /\ depth  = [n \in Node |-> IF n = Root THEN 0 ELSE Infinity]
  /\ parent = [n \in Node |-> n]
  /\ msgs   = [n \in Node |->
                 IF n \in Nbrs(Root)
                   THEN << [src |-> Root, d |-> 0] >>
                   ELSE << >>]

Receive(n) ==
  /\ msgs[n] # << >>
  /\ LET m == Head(msgs[n]) IN
       IF m.d + 1 < depth[n]
         THEN /\ depth'  = [depth  EXCEPT ![n] = m.d + 1]
              /\ parent' = [parent EXCEPT ![n] = m.src]
              /\ msgs'   = [k \in Node |->
                              IF k = n THEN Tail(msgs[n])
                              ELSE IF k \in Nbrs(n)
                                THEN Append(msgs[k],
                                            [src |-> n, d |-> m.d + 1])
                                ELSE msgs[k]]
         ELSE /\ msgs' = [msgs EXCEPT ![n] = Tail(msgs[n])]
              /\ UNCHANGED <<depth, parent>>

Next == \E n \in Node : Receive(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Recursive path and distance definitions                                 *)
(***************************************************************************)
RECURSIVE Reach(_)
Reach(k) == IF k = 0 THEN {Root}
            ELSE LET R == Reach(k - 1)
                 IN  R \cup UNION {Nbrs(m) : m \in R}

Distance(n) ==
  IF \E k \in 0..N : n \in Reach(k)
    THEN CHOOSE k \in 0..N : /\ n \in Reach(k)
                             /\ \A j \in 0..(k - 1) : n \notin Reach(j)
    ELSE Infinity

\* Length of the path obtained by following parent pointers to Root
RECURSIVE ParentDist(_, _)
ParentDist(n, k) ==
  IF n = Root THEN 0
  ELSE IF k = 0 \/ parent[n] = n THEN Infinity
  ELSE LET d == ParentDist(parent[n], k - 1)
       IN  IF d = Infinity THEN Infinity ELSE d + 1

PathLength(n) == ParentDist(n, N)

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
  /\ depth  \in [Node -> 0..Infinity]
  /\ parent \in [Node -> Node]
  /\ msgs   \in [Node -> Seq(Msg)]
  /\ \A n \in Node : \A i \in 1..Len(msgs[n]) :
        /\ msgs[n][i] \in Msg
        /\ msgs[n][i].src \in Nbrs(n)
        /\ msgs[n][i].d < Infinity

Terminated == \A n \in Node : msgs[n] = << >>

Postcondition ==
  \A n \in Node : /\ PathLength(n) = Distance(n)
                  /\ depth[n] = Distance(n)

Termination == <>Terminated

Correctness == [](Terminated => Postcondition)

THEOREM Spec => []TypeOK /\ Termination /\ Correctness
=============================================================================