------------------------------- MODULE MCSession10set -------------------------------
(***************************************************************************)
(* Model-checking wrapper for the Session10set system: a distributed      *)
(* breadth-first spanning-tree construction. Each node keeps a depth and   *)
(* a parent. Messages are held as sets. The base system is included here  *)
(* so that the module is self-contained and parses on its own.             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Edges, Root

ASSUME RootInNodes == Root \in Nodes
ASSUME EdgesWellFormed == Edges \subseteq (Nodes \X Nodes)

VARIABLES depth, parent, msgs

vars == << depth, parent, msgs >>

N == Cardinality(Nodes)          \* stands for "infinite" / unreached depth

Nbrs(n) == { m \in Nodes : << n, m >> \in Edges \/ << m, n >> \in Edges }

-----------------------------------------------------------------------------
(* Base system (Session10set)                                              *)
-----------------------------------------------------------------------------
Init ==
  /\ depth  = [n \in Nodes |-> IF n = Root THEN 0 ELSE N]
  /\ parent = [n \in Nodes |-> n]
  /\ msgs   = [n \in Nodes |-> IF n \in Nbrs(Root) THEN { << Root, 0 >> } ELSE {}]

Receive(n) ==
  \E m \in msgs[n] :
    LET d == m[2] + 1 IN
      IF d < depth[n]
        THEN /\ depth'  = [depth  EXCEPT ![n] = d]
             /\ parent' = [parent EXCEPT ![n] = m[1]]
             /\ msgs'   = [k \in Nodes |->
                             IF k = n THEN msgs[n] \ {m}
                             ELSE IF k \in Nbrs(n) THEN msgs[k] \cup { << n, d >> }
                             ELSE msgs[k]]
        ELSE /\ msgs' = [msgs EXCEPT ![n] = msgs[n] \ {m}]
             /\ UNCHANGED << depth, parent >>

-----------------------------------------------------------------------------
(* Termination: all message queues are empty                              *)
-----------------------------------------------------------------------------
Terminated == \A n \in Nodes : msgs[n] = {}

Done == Terminated /\ UNCHANGED vars

Next == (\E n \in Nodes : Receive(n)) \/ Done

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(\E n \in Nodes : Receive(n))

-----------------------------------------------------------------------------
(* Type correctness                                                        *)
-----------------------------------------------------------------------------
TypeOK ==
  /\ depth  \in [Nodes -> 0..N]
  /\ parent \in [Nodes -> Nodes]
  /\ msgs   \in [Nodes -> SUBSET (Nodes \X (0..N))]

-----------------------------------------------------------------------------
(* Parent paths                                                            *)
-----------------------------------------------------------------------------
\* Sequence of nodes following parent pointers from n towards Root,
\* bounded by k steps. Returns <<>> if Root is not reached.
RECURSIVE ParentPath(_, _)
ParentPath(n, k) ==
  IF n = Root THEN << Root >>
  ELSE IF k = 0 \/ parent[n] = n THEN << >>
  ELSE LET p == ParentPath(parent[n], k - 1)
       IN IF p = << >> THEN << >> ELSE << n >> \o p

\* Length (in edges) of the parent path from n to Root; N if no such path.
RECURSIVE PathDepth(_, _)
PathDepth(n, k) ==
  IF n = Root THEN 0
  ELSE IF k = 0 \/ parent[n] = n THEN N
  ELSE LET d == PathDepth(parent[n], k - 1)
       IN IF d >= N THEN N ELSE d + 1

ParentDepth(n) == PathDepth(n, N)

-----------------------------------------------------------------------------
(* Graph distance from Root                                                *)
-----------------------------------------------------------------------------
RECURSIVE Within(_)
Within(k) ==
  IF k = 0 THEN { Root }
  ELSE LET W == Within(k - 1)
       IN W \cup UNION { Nbrs(m) : m \in W }

Distance(n) ==
  IF n \in Within(N)
    THEN CHOOSE k \in 0..N : /\ n \in Within(k)
                             /\ (k = 0 \/ n \notin Within(k - 1))
    ELSE N

-----------------------------------------------------------------------------
(* Correctness                                                             *)
-----------------------------------------------------------------------------
Correct ==
  Terminated => \A n \in Nodes : ParentDepth(n) = Distance(n)

EventuallyTerminates == <>Terminated

THEOREM Spec => [](TypeOK /\ Correct)
THEOREM FairSpec => EventuallyTerminates
=============================================================================