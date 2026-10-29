------------------------------- MODULE Paths -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Edges, root, MaxNodes

(***************************************************************************)
(* Graph operators                                                         *)
(***************************************************************************)
Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

SetNbrs(S) == UNION {Nbrs(n) : n \in S}

(* Declarative definition: the smallest set of nodes that contains S and   *)
(* is closed under taking neighbors.                                        *)
ReachableFrom(S) ==
  CHOOSE R \in SUBSET Nodes :
    /\ S \subseteq R
    /\ SetNbrs(R) \subseteq R
    /\ \A T \in SUBSET Nodes :
          (S \subseteq T /\ SetNbrs(T) \subseteq T) => R \subseteq T

(* Executable recursive definition.                                         *)
RECURSIVE RF(_)
RF(S) == LET R == S \cup SetNbrs(S)
         IN  IF R = S THEN S ELSE RF(R)

THEOREM RFEquivalence ==
  \A S \in SUBSET Nodes : IsFiniteSet(Nodes) => RF(S) = ReachableFrom(S)

ASSUME /\ \A e \in Edges : e \subseteq Nodes /\ Cardinality(e) = 2
       /\ root \in Nodes
       /\ MaxNodes \in Nat
       /\ Cardinality(Nodes) <= MaxNodes
       /\ RF({root}) = Nodes

(***************************************************************************)
(* Distributed algorithm: each node process receives messages carrying a   *)
(* sender and its depth; on finding a shorter path it updates its depth    *)
(* and parent and sends its new depth to all neighbors.                    *)
(***************************************************************************)
Msg == Nodes \X (0..MaxNodes)

Queues == [Nodes -> Seq(Msg)]

VARIABLES msgs, depth, parent

vars == <<msgs, depth, parent>>

TypeOK ==
  /\ msgs \in Queues
  /\ depth \in [Nodes -> 0..MaxNodes]
  /\ parent \in [Nodes -> Nodes]

Init ==
  /\ depth = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes]
  /\ parent = [n \in Nodes |-> n]
  /\ msgs = [n \in Nodes |-> IF n \in Nbrs(root) THEN << <<root, 0>> >>
                                                 ELSE << >>]

proc(n) ==
  /\ msgs[n] # << >>
  /\ LET m  == Head(msgs[n])
         nd == m[2] + 1
     IN  IF nd < depth[n]
           THEN /\ depth' = [depth EXCEPT ![n] = nd]
                /\ parent' = [parent EXCEPT ![n] = m[1]]
                /\ msgs' = [k \in Nodes |->
                              IF k = n THEN Tail(msgs[n])
                              ELSE IF k \in Nbrs(n)
                                     THEN Append(msgs[k], <<n, nd>>)
                                     ELSE msgs[k]]
           ELSE /\ msgs' = [msgs EXCEPT ![n] = Tail(msgs[n])]
                /\ UNCHANGED <<depth, parent>>

Terminating ==
  /\ \A n \in Nodes : msgs[n] = << >>
  /\ UNCHANGED vars

Next == (\E n \in Nodes : proc(n)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A n \in Nodes : WF_vars(proc(n))

(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)
Done == \A n \in Nodes : msgs[n] = << >>

ParentOK ==
  \A n \in Nodes \ {root} :
     depth[n] < MaxNodes => (parent[n] \in Nbrs(n) /\ depth[parent[n]] < depth[n])

Correct ==
  Done => \A n \in Nodes \ {root} :
            /\ parent[n] \in Nbrs(n)
            /\ depth[n] = depth[parent[n]] + 1

Termination == <>Done
=============================================================================