---------------------------- MODULE SpanningTreeTermination ----------------------------
(***************************************************************************)
(* Distributed spanning-tree construction with termination (quiescence).  *)
(* Each node keeps a depth estimate and a parent pointer.  Nodes exchange   *)
(* depth values over FIFO queues, one per directed edge.  A node that       *)
(* receives a value d with d + 1 < depth adopts depth d + 1, makes the      *)
(* sender its parent and announces the new depth to all neighbours.         *)
(* Depths only decrease, so each queue holds a strictly decreasing sequence *)
(* whose elements are all >= the sender's current depth.                    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes,      \* finite set of nodes
          Edges,      \* set of directed pairs; symmetric (undirected graph)
          Root        \* designated root

MaxCard == Cardinality(Nodes)   \* serves as "infinity" for depth

Nbrs(n) == { m \in Nodes : <<n, m>> \in Edges }

(* Nodes reachable from Root in at most k hops *)
Reach[k \in Nat] ==
  IF k = 0 THEN {Root}
  ELSE Reach[k-1] \cup { m \in Nodes : \E n \in Reach[k-1] : <<n, m>> \in Edges }

ASSUME TopologyAssumptions ==
  /\ IsFiniteSet(Nodes)
  /\ Root \in Nodes
  /\ Edges \subseteq Nodes \X Nodes
  /\ \A n \in Nodes : <<n, n>> \notin Edges                    \* no self loops
  /\ \A n, m \in Nodes : <<n, m>> \in Edges => <<m, n>> \in Edges \* undirected
  /\ Reach[MaxCard] = Nodes                                     \* connected

(* Graph distance (number of hops) from n to Root *)
Dist(n) == CHOOSE k \in 0..MaxCard :
              /\ n \in Reach[k]
              /\ \A j \in 0..(k-1) : n \notin Reach[j]

VARIABLES depth, parent, msgs

vars == <<depth, parent, msgs>>

-----------------------------------------------------------------------------
Init ==
  /\ depth  = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCard]
  /\ parent = [n \in Nodes |-> Root]
  /\ msgs   = [e \in Edges |-> IF e[1] = Root THEN <<0>> ELSE <<>>]

(* Node m receives the head message on queue n -> m *)
Receive(n, m) ==
  /\ <<n, m>> \in Edges
  /\ msgs[<<n, m>>] # <<>>
  /\ LET d    == Head(msgs[<<n, m>>])
         rest == [msgs EXCEPT ![<<n, m>>] = Tail(@)]
     IN  IF d + 1 < depth[m]
           THEN /\ depth'  = [depth EXCEPT ![m] = d + 1]
                /\ parent' = [parent EXCEPT ![m] = n]
                /\ msgs'   = [e \in Edges |->
                                IF e[1] = m THEN Append(rest[e], d + 1)
                                            ELSE rest[e]]
           ELSE /\ msgs' = rest
                /\ UNCHANGED <<depth, parent>>

Quiescent == \A e \in Edges : msgs[e] = <<>>

(* Explicit stuttering once terminated (avoids spurious deadlock) *)
Terminated == Quiescent /\ UNCHANGED vars

Next == \/ \E e \in Edges : Receive(e[1], e[2])
        \/ Terminated

Fairness == \A e \in Edges : WF_vars(Receive(e[1], e[2]))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
  /\ depth  \in [Nodes -> 0..MaxCard]
  /\ parent \in [Nodes -> Nodes]
  /\ msgs   \in [Edges -> Seq(0..MaxCard)]

DepthBounded ==
  /\ depth[Root] = 0
  /\ \A n \in Nodes : depth[n] \in 0..MaxCard

ParentValid ==
  \A n \in Nodes : parent[n] \in Nbrs(n) \cup {Root}

QueuesDecreasing ==
  \A e \in Edges :
     LET s == msgs[e] IN
       /\ \A i \in 1..(Len(s) - 1) : s[i] > s[i+1]
       /\ \A i \in 1..Len(s) : s[i] >= depth[e[1]]

DepthLowerBound ==
  \A n \in Nodes : depth[n] >= Dist(n)

TreeConsistent ==
  \A n \in Nodes \ {Root} :
     depth[n] < MaxCard => /\ parent[n] \in Nbrs(n)
                           /\ depth[parent[n]] < depth[n]

Inv == /\ TypeOK
       /\ DepthBounded
       /\ ParentValid
       /\ QueuesDecreasing
       /\ DepthLowerBound
       /\ TreeConsistent

-----------------------------------------------------------------------------
(* Final postcondition *)

RECURSIVE Anc(_, _)
Anc(k, n) == IF k = 0 THEN n ELSE Anc(k - 1, parent[n])

PostCondition ==
  /\ \A n \in Nodes : depth[n] = Dist(n)
  /\ \A n \in Nodes \ {Root} :
        /\ parent[n] \in Nbrs(n)
        /\ depth[n] = depth[parent[n]] + 1
  /\ \A n \in Nodes :
        /\ Anc(depth[n], n) = Root
        /\ \A k \in 0..(depth[n] - 1) : Anc(k, n) # Root

FinalCorrectness == Quiescent => PostCondition

-----------------------------------------------------------------------------
(* Liveness *)

Termination      == <>Quiescent
StableQuiescence == <>[]Quiescent
EventuallyTree   == <>[](Quiescent /\ PostCondition)

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => []FinalCorrectness
THEOREM Spec => Termination
THEOREM Spec => StableQuiescence
THEOREM Spec => EventuallyTree
=============================================================================