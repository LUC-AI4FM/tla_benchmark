---------------------------- MODULE MCSession10 ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Edges, root, MaxNodes

ASSUME root \in Nodes
ASSUME MaxNodes \in Nat
ASSUME \A e \in Edges : e \subseteq Nodes

VARIABLES depth, parent, msgs

vars == <<depth, parent, msgs>>

Nbrs(n) == {m \in Nodes : {m, n} \in Edges /\ m # n}

Msg == [src : Nodes, d : 0..MaxNodes]

-----------------------------------------------------------------------------
Init ==
  /\ depth  = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes]
  /\ parent = [n \in Nodes |-> n]
  /\ msgs   = [n \in Nodes |-> IF n \in Nbrs(root)
                                 THEN << [src |-> root, d |-> 0] >>
                                 ELSE << >>]

Receive(n) ==
  /\ msgs[n] # << >>
  /\ LET m == Head(msgs[n])
         nd == m.d + 1
     IN  IF nd < depth[n]
           THEN /\ depth'  = [depth EXCEPT ![n] = nd]
                /\ parent' = [parent EXCEPT ![n] = m.src]
                /\ msgs' = [k \in Nodes |->
                              IF k = n THEN Tail(msgs[n])
                              ELSE IF k \in Nbrs(n)
                                     THEN Append(msgs[k], [src |-> n, d |-> nd])
                                     ELSE msgs[k]]
           ELSE /\ msgs' = [msgs EXCEPT ![n] = Tail(msgs[n])]
                /\ UNCHANGED <<depth, parent>>

Terminated == \A n \in Nodes : msgs[n] = << >>

Done == Terminated /\ UNCHANGED vars

Next == (\E n \in Nodes : Receive(n)) \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Graph distance to the root, computed by recursive BFS layering *)
RECURSIVE Within(_)
Within(k) == IF k = 0 THEN {root}
             ELSE Within(k-1) \cup UNION {Nbrs(x) : x \in Within(k-1)}

Reachable(n) == \E k \in 0..MaxNodes : n \in Within(k)

Distance(n) ==
  IF Reachable(n)
    THEN CHOOSE k \in 0..MaxNodes :
           /\ n \in Within(k)
           /\ \A j \in 0..(k-1) : n \notin Within(j)
    ELSE MaxNodes

(* Length of the path obtained by following parent pointers to the root *)
RECURSIVE PL(_, _)
PL(n, fuel) ==
  IF n = root THEN 0
  ELSE IF fuel = 0 \/ parent[n] = n THEN MaxNodes
  ELSE 1 + PL(parent[n], fuel - 1)

PathLen(n) == PL(n, MaxNodes)

Post ==
  \A n \in Nodes :
     IF Reachable(n)
       THEN /\ PathLen(n) = Distance(n)
            /\ depth[n] = Distance(n)
       ELSE /\ depth[n] = MaxNodes
            /\ parent[n] = n

-----------------------------------------------------------------------------
TypeOK ==
  /\ depth  \in [Nodes -> 0..MaxNodes]
  /\ parent \in [Nodes -> Nodes]
  /\ msgs   \in [Nodes -> Seq(Msg)]
  /\ \A n \in Nodes : \A i \in 1..Len(msgs[n]) :
        /\ msgs[n][i].src \in Nodes
        /\ msgs[n][i].d \in 0..MaxNodes

Termination == <>Terminated

DepthCorrect == Terminated => Post

=============================================================================