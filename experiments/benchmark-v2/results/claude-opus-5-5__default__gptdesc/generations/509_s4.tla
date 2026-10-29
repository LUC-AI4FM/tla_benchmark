------------------------------- MODULE Session10MC -------------------------------
(***************************************************************************)
(* Model-checking wrapper for a distributed shortest-path spanning tree   *)
(* construction (as in Session10).  Each node keeps a depth estimate, a   *)
(* parent pointer and an inbox (message queue).  The root starts at depth *)
(* 0 and advertises its depth to its neighbours.  When a node learns of a *)
(* shorter depth, it adopts the sender as parent and re-advertises.       *)
(*                                                                         *)
(* Properties checked:                                                    *)
(*   - Termination : eventually all message queues are empty              *)
(*   - TypeOK      : type correctness of state variables and messages     *)
(*   - Correctness : termination implies the postcondition, i.e. the      *)
(*                   recursive parent path from every node to the root    *)
(*                   has length equal to the graph distance to the root   *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes,      \* set of nodes of the graph
          Root,       \* distinguished root node
          Edges,      \* set of (symmetric) edges, as pairs <<a, b>>
          NoParent    \* model value: parent of a node not (yet) in the tree

ASSUME /\ Root \in Nodes
       /\ Edges \subseteq Nodes \X Nodes
       /\ \A e \in Edges : <<e[2], e[1]>> \in Edges
       /\ NoParent \notin Nodes

VARIABLES depth, parent, msgs

vars == <<depth, parent, msgs>>

N   == Cardinality(Nodes)
Inf == N   \* larger than any possible graph distance (at most N-1)

Neighbors(n) == {m \in Nodes : <<n, m>> \in Edges /\ m # n}

Msg == [from : Nodes, d : 0..Inf]

(***************************************************************************)
(* Graph distance                                                          *)
(***************************************************************************)
RECURSIVE Within(_)
Within(k) == IF k = 0
               THEN {Root}
               ELSE Within(k-1) \cup
                      {m \in Nodes : \E x \in Within(k-1) : <<x, m>> \in Edges}

Reachable == Within(N)

Dist(n) == IF n \in Reachable
             THEN CHOOSE k \in 0..N :
                     /\ n \in Within(k)
                     /\ (k = 0 \/ n \notin Within(k-1))
             ELSE Inf

(***************************************************************************)
(* Recursive path along parent pointers (bounded to avoid cycles)         *)
(***************************************************************************)
RECURSIVE PathLen(_, _)
PathLen(n, k) ==
    IF n = Root THEN 0
    ELSE IF k = 0 \/ parent[n] = NoParent THEN Inf
    ELSE 1 + PathLen(parent[n], k - 1)

ParentPathLen(n) == PathLen(n, N)

RECURSIVE PathFrom(_, _)
PathFrom(n, k) ==
    IF n = Root \/ k = 0 \/ parent[n] = NoParent
      THEN <<n>>
      ELSE <<n>> \o PathFrom(parent[n], k - 1)

\* A recursive path is a valid graph path ending at the root
IsRootPath(p) ==
    /\ Len(p) >= 1
    /\ p[Len(p)] = Root
    /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in Edges

(***************************************************************************)
(* Protocol                                                                *)
(***************************************************************************)
Init ==
    /\ depth  = [n \in Nodes |-> IF n = Root THEN 0 ELSE Inf]
    /\ parent = [n \in Nodes |-> NoParent]
    /\ msgs   = [n \in Nodes |->
                   IF n \in Neighbors(Root)
                     THEN << [from |-> Root, d |-> 0] >>
                     ELSE << >>]

Receive(n) ==
    /\ msgs[n] # << >>
    /\ LET m == Head(msgs[n]) IN
         IF m.d + 1 < depth[n]
           THEN /\ depth'  = [depth  EXCEPT ![n] = m.d + 1]
                /\ parent' = [parent EXCEPT ![n] = m.from]
                /\ msgs'   = [k \in Nodes |->
                                IF k = n THEN Tail(msgs[n])
                                ELSE IF k \in Neighbors(n)
                                  THEN Append(msgs[k], [from |-> n, d |-> m.d + 1])
                                  ELSE msgs[k]]
           ELSE /\ msgs' = [msgs EXCEPT ![n] = Tail(msgs[n])]
                /\ UNCHANGED <<depth, parent>>

Termination == \A n \in Nodes : msgs[n] = << >>

Done == Termination /\ UNCHANGED vars

Next == (\E n \in Nodes : Receive(n)) \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(\E n \in Nodes : Receive(n))

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
    /\ depth  \in [Nodes -> 0..Inf]
    /\ parent \in [Nodes -> Nodes \cup {NoParent}]
    /\ msgs   \in [Nodes -> Seq(Msg)]
    /\ \A n \in Nodes : \A i \in 1..Len(msgs[n]) : msgs[n][i] \in Msg

Terminates == <>Termination

Postcondition ==
    \A n \in Nodes :
        /\ ParentPathLen(n) = Dist(n)
        /\ depth[n] = Dist(n)
        /\ n \in Reachable => IsRootPath(PathFrom(n, N))

Correctness == Termination => Postcondition

THEOREM Spec => []TypeOK
THEOREM Spec => []Correctness
THEOREM Spec => Terminates
================================================================================