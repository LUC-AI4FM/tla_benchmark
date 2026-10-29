------------------------------- MODULE YoYoPruning -------------------------------
(***************************************************************************)
(* Yo-Yo leader election with pruning on an undirected, loop-free,        *)
(* connected graph over a fixed, finite set of numbered nodes.             *)
(*                                                                         *)
(* The initial state picks a connected graph over Nodes nondeterministically*)
(* and orients every edge from the smaller to the larger endpoint.         *)
(* Each node then runs rounds that consist of a "down" phase and an "up"   *)
(* phase:                                                                  *)
(*  - Down phase: a source sends its own identity to all of its            *)
(*    out-neighbors. Any other node waits for values from all of its       *)
(*    in-neighbors, computes their minimum and forwards it to its          *)
(*    out-neighbors.                                                       *)
(*  - Up phase: a sink replies to every in-neighbor. The reply is "yes"    *)
(*    if that neighbor sent the minimum value and "no" otherwise. An       *)
(*    internal node or a source waits for replies from all of its          *)
(*    out-neighbors. If it got any "no", it answers "no" to all of its     *)
(*    in-neighbors. Every edge that carried a "no" is reversed.            *)
(*  - Pruning: a sink with a single in-neighbor asks that neighbor to      *)
(*    prune the edge and then deactivates itself. A node that received the *)
(*    same value from several in-neighbors asks all but one of them to     *)
(*    prune their edge.                                                    *)
(* The algorithm terminates when the only active node, the leader, has no  *)
(* edges left.                                                             *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

CONSTANT Nodes

ASSUME NodesAssumption ==
    /\ Nodes \subseteq Int
    /\ Nodes # {}
    /\ IsFiniteSet(Nodes)

VARIABLES
    active,   \* active[n]: is node n still participating?
    nbrs,     \* nbrs[n]: function from n's neighbors to "in"/"out" (n's local view)
    phase,    \* phase[n] \in {"down", "up"}
    mins,     \* mins[n]: minimum value n received in the current down phase
    rcvd,     \* rcvd[n]: down messages consumed by n in the current round
    msgs      \* msgs[n]: messages delivered to n and not yet consumed

vars == <<active, nbrs, phase, mins, rcvd, msgs>>

-----------------------------------------------------------------------------
(* Auxiliary definitions *)

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

MinNode == Min(Nodes)

PossibleEdges == {e \in SUBSET Nodes : Cardinality(e) = 2}

RECURSIVE Reach(_, _)
Reach(E, S) ==
    LET S2 == S \cup {m \in Nodes : \E n \in S : {m, n} \in E}
    IN  IF S2 = S THEN S ELSE Reach(E, S2)

IsConnected(E) == \A n \in Nodes : Reach(E, {n}) = Nodes

Msgs == [phase : {"down", "up"},
         sndr  : Nodes,
         val   : Nodes,
         reply : {"yes", "no", "none"},
         prune : BOOLEAN]

DownMsg(s, v) ==
    [phase |-> "down", sndr |-> s, val |-> v, reply |-> "none", prune |-> FALSE]

UpMsg(s, v, r, p) ==
    [phase |-> "up", sndr |-> s, val |-> v, reply |-> r, prune |-> p]

Neighbors(n) == DOMAIN nbrs[n]
Incoming(n)  == {m \in Neighbors(n) : nbrs[n][m] = "in"}
Outgoing(n)  == {m \in Neighbors(n) : nbrs[n][m] = "out"}

\* value that in-neighbor m sent to n in the current round
ValOf(n, m) == (CHOOSE x \in rcvd[n] : x.sndr = m).val

\* m is the representative among in-neighbors of n that sent the same value
Keep(n, m) ==
    m = Min({k \in Incoming(n) : ValOf(n, k) = ValOf(n, m)})

PruneIn(n, m, leaf) == leaf \/ ~Keep(n, m)

ReplyTo(n, m, noAll) ==
    IF ~noAll /\ ValOf(n, m) = mins[n] THEN "yes" ELSE "no"

EmptyFun == [m \in {} |-> "in"]

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ \E E \in SUBSET PossibleEdges :
          /\ IsConnected(E)
          /\ nbrs = [n \in Nodes |->
                       [m \in {k \in Nodes : {k, n} \in E} |->
                           IF m < n THEN "in" ELSE "out"]]
    /\ active = [n \in Nodes |-> TRUE]
    /\ phase  = [n \in Nodes |-> "down"]
    /\ mins   = [n \in Nodes |-> n]
    /\ rcvd   = [n \in Nodes |-> {}]
    /\ msgs   = [n \in Nodes |-> {}]

-----------------------------------------------------------------------------
(* Down phase *)

DownSource(n) ==
    /\ active[n]
    /\ phase[n] = "down"
    /\ Incoming(n) = {}
    /\ Outgoing(n) # {}
    /\ mins'  = [mins EXCEPT ![n] = n]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ rcvd'  = [rcvd EXCEPT ![n] = {}]
    /\ msgs'  = [m \in Nodes |->
                   IF m \in Outgoing(n) THEN msgs[m] \cup {DownMsg(n, n)}
                   ELSE msgs[m]]
    /\ UNCHANGED <<active, nbrs>>

DownOther(n) ==
    /\ active[n]
    /\ phase[n] = "down"
    /\ Incoming(n) # {}
    /\ LET dm == {x \in msgs[n] : x.phase = "down"}
       IN  /\ {x.sndr : x \in dm} = Incoming(n)
           /\ LET mn == Min({x.val : x \in dm})
              IN  /\ mins'  = [mins EXCEPT ![n] = mn]
                  /\ phase' = [phase EXCEPT ![n] = "up"]
                  /\ rcvd'  = [rcvd EXCEPT ![n] = dm]
                  /\ msgs'  = [m \in Nodes |->
                                 IF m = n THEN msgs[n] \ dm
                                 ELSE IF m \in Outgoing(n)
                                      THEN msgs[m] \cup {DownMsg(n, mn)}
                                      ELSE msgs[m]]
    /\ UNCHANGED <<active, nbrs>>

-----------------------------------------------------------------------------
(* Up phase *)

UpSink(n) ==
    /\ active[n]
    /\ phase[n] = "up"
    /\ Outgoing(n) = {}
    /\ Incoming(n) # {}
    /\ LET In   == Incoming(n)
           leaf == Cardinality(In) = 1
           newIn == {k \in In : ~PruneIn(n, k, leaf)}
       IN  /\ msgs' = [m \in Nodes |->
                         IF m \in In
                         THEN msgs[m] \cup
                                {UpMsg(n, mins[n], ReplyTo(n, m, FALSE),
                                       PruneIn(n, m, leaf))}
                         ELSE msgs[m]]
           /\ nbrs' = [nbrs EXCEPT ![n] =
                         IF leaf THEN EmptyFun
                         ELSE [m \in newIn |->
                                 IF ReplyTo(n, m, FALSE) = "no"
                                 THEN "out" ELSE "in"]]
           /\ active' = [active EXCEPT ![n] = ~leaf]
    /\ phase' = [phase EXCEPT ![n] = "down"]
    /\ rcvd'  = [rcvd EXCEPT ![n] = {}]
    /\ UNCHANGED mins

UpOther(n) ==
    /\ active[n]
    /\ phase[n] = "up"
    /\ Outgoing(n) # {}
    /\ LET um == {x \in msgs[n] : x.phase = "up"}
       IN  /\ {x.sndr : x \in um} = Outgoing(n)
           /\ LET In     == Incoming(n)
                  Out    == Outgoing(n)
                  noAll  == \E x \in um : x.reply = "no"
                  upOf(m) == CHOOSE x \in um : x.sndr = m
                  newIn  == {k \in In : ~PruneIn(n, k, FALSE)}
                  newOut == {k \in Out : ~upOf(k).prune}
              IN  /\ msgs' = [m \in Nodes |->
                                IF m = n THEN msgs[n] \ um
                                ELSE IF m \in In
                                     THEN msgs[m] \cup
                                            {UpMsg(n, mins[n],
                                                   ReplyTo(n, m, noAll),
                                                   PruneIn(n, m, FALSE))}
                                     ELSE msgs[m]]
                  /\ nbrs' = [nbrs EXCEPT ![n] =
                                [m \in newIn \cup newOut |->
                                   IF m \in newIn
                                   THEN IF ReplyTo(n, m, noAll) = "no"
                                        THEN "out" ELSE "in"
                                   ELSE IF upOf(m).reply = "no"
                                        THEN "in" ELSE "out"]]
    /\ phase' = [phase EXCEPT ![n] = "down"]
    /\ rcvd'  = [rcvd EXCEPT ![n] = {}]
    /\ UNCHANGED <<active, mins>>

-----------------------------------------------------------------------------
(* Next-state relation and specification *)

Next ==
    \E n \in Nodes :
        \/ DownSource(n)
        \/ DownOther(n)
        \/ UpSink(n)
        \/ UpOther(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ DOMAIN nbrs = Nodes
    /\ \A n \in Nodes :
          /\ Neighbors(n) \subseteq Nodes \ {n}
          /\ \A m \in Neighbors(n) : nbrs[n][m] \in {"in", "out"}
    /\ phase \in [Nodes -> {"down", "up"}]
    /\ mins  \in [Nodes -> Nodes]
    /\ rcvd  \in [Nodes -> SUBSET Msgs]
    /\ msgs  \in [Nodes -> SUBSET Msgs]

\* deactivated nodes have no edges left
InactiveIsolated ==
    \A n \in Nodes : ~active[n] => Neighbors(n) = {}

\* the node with the smallest identity is never deactivated
MinNodeActive == active[MinNode]

\* there always remains at least one active node
SomeActive == \E n \in Nodes : active[n]

\* two active nodes that are both in the down phase agree on their shared edge
ConsistentDown ==
    \A m, n \in Nodes :
        (active[m] /\ active[n] /\ phase[m] = "down" /\ phase[n] = "down") =>
            /\ (m \in Neighbors(n) <=> n \in Neighbors(m))
            /\ m \in Neighbors(n) => nbrs[n][m] # nbrs[m][n]

\* an active node in the down phase only has active neighbors
DownNeighborsActive ==
    \A n \in Nodes :
        (active[n] /\ phase[n] = "down") =>
            \A m \in Neighbors(n) : active[m]

Terminated ==
    \A n \in Nodes : active[n] => Neighbors(n) = {}

\* on termination, exactly the minimum node remains active (the leader)
LeaderElected ==
    Terminated => \A n \in Nodes : active[n] <=> n = MinNode

-----------------------------------------------------------------------------
(* Liveness and the characterization of termination *)

Liveness == <>Terminated

\* termination states are exactly the deadlock states
TerminationIsDeadlock == [](Terminated <=> ~ENABLED Next)

THEOREM Spec => []TypeOK
THEOREM Spec => [](InactiveIsolated /\ MinNodeActive /\ SomeActive)
THEOREM Spec => []LeaderElected
THEOREM Spec => Liveness
THEOREM Spec => TerminationIsDeadlock

==============================================================================