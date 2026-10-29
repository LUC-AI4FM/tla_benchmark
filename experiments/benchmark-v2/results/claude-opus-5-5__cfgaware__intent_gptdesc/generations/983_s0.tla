------------------------------ MODULE GraphPruning ------------------------------
(***************************************************************************)
(* Distributed leaf-pruning protocol on a fixed, connected, undirected     *)
(* graph.                                                                  *)
(*                                                                         *)
(* All processors start active. An active processor that is not a          *)
(* designated terminal may deactivate (prune) itself only when it knows of *)
(* at most one active neighbour, i.e. it is a leaf of the active subgraph. *)
(* Its knowledge is a superset of its truly active neighbours, because     *)
(* "removed" notices may still be in transit. When it prunes it sends a    *)
(* "removed" message on every incident edge. Each channel is a reliable    *)
(* FIFO queue: no message is lost or corrupted, but delivery is            *)
(* asynchronous.                                                           *)
(*                                                                         *)
(* Removing a leaf never disconnects the remaining active subgraph.        *)
(* Terminals are never removed, so all terminals stay connected.           *)
(*                                                                         *)
(* Termination holds once every channel is empty and no processor is       *)
(* eligible to prune. The flag `finished` is kept equal to that condition. *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

\* The fixed graph and terminal set (connected graph, non-empty terminals).
Nodes     == 1..6
Edges     == { {1,2}, {2,3}, {3,4}, {2,5}, {5,6}, {3,5} }
Terminals == {1, 4}

Nbr(n)   == { m \in Nodes : {n, m} \in Edges }
DirEdges == { e \in Nodes \X Nodes : {e[1], e[2]} \in Edges }

Msg == {"removed"}

VARIABLES active,    \* set of currently active processors
          known,     \* known[n] : neighbours n still believes active
          chan,      \* chan[<<m,n>>] : FIFO queue of messages from m to n
          finished   \* TRUE iff the protocol has terminated

vars == <<active, known, chan, finished>>

-----------------------------------------------------------------------------
(* Connectivity helpers *)
RECURSIVE ReachFrom(_, _)
ReachFrom(S, R) ==
    LET N == R \cup { m \in S : \E r \in R : {r, m} \in Edges }
    IN  IF N = R THEN R ELSE ReachFrom(S, N)

Connected(S) == \A s \in S : ReachFrom(S, {s}) = S

-----------------------------------------------------------------------------
(* Local enabling condition for pruning *)
CanPruneW(n, act, kn) ==
    /\ n \in act
    /\ n \notin Terminals
    /\ Cardinality(kn[n]) <= 1

TermCond(act, kn, ch) ==
    /\ \A e \in DirEdges : ch[e] = << >>
    /\ ~ \E n \in Nodes : CanPruneW(n, act, kn)

Terminated == TermCond(active, known, chan)

-----------------------------------------------------------------------------
TypeOK ==
    /\ active \subseteq Nodes
    /\ known \in [Nodes -> SUBSET Nodes]
    /\ \A n \in Nodes : known[n] \subseteq Nbr(n)
    /\ chan \in [DirEdges -> Seq(Msg)]
    /\ \A e \in DirEdges : Len(chan[e]) <= 1
    /\ finished \in BOOLEAN

Init ==
    /\ active = Nodes
    /\ known  = [n \in Nodes |-> Nbr(n)]
    /\ chan   = [e \in DirEdges |-> << >>]
    /\ finished = TermCond(Nodes, [n \in Nodes |-> Nbr(n)],
                           [e \in DirEdges |-> << >>])

(* A processor deactivates itself and notifies all neighbours. *)
Prune(n) ==
    /\ CanPruneW(n, active, known)
    /\ active' = active \ {n}
    /\ chan' = [e \in DirEdges |->
                  IF e[1] = n THEN Append(chan[e], "removed") ELSE chan[e]]
    /\ UNCHANGED known
    /\ finished' = TermCond(active', known, chan')

(* Processor n receives the head message on the edge from m. *)
Receive(m, n) ==
    /\ <<m, n>> \in DirEdges
    /\ chan[<<m, n>>] # << >>
    /\ Head(chan[<<m, n>>]) = "removed"
    /\ known' = [known EXCEPT ![n] = @ \ {m}]
    /\ chan'  = [chan EXCEPT ![<<m, n>>] = Tail(@)]
    /\ UNCHANGED active
    /\ finished' = TermCond(active, known', chan')

(* Stable configuration: stuttering only. *)
Done == finished /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes : Prune(n)
    \/ \E m, n \in Nodes : Receive(m, n)
    \/ Done

Fairness ==
    /\ \A n \in Nodes : WF_vars(Prune(n))
    /\ \A m, n \in Nodes : WF_vars(Receive(m, n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Invariants *)

(* What a processor believes about its neighbours is exact up to          *)
(* in-transit removal notices: it believes in every truly active          *)
(* neighbour, and also in every pruned neighbour whose notice is pending. *)
NeighborInv ==
    \A n \in Nodes :
        known[n] = (Nbr(n) \cap active)
                   \cup { m \in Nbr(n) : chan[<<m, n>>] # << >> }

(* The termination flag is set exactly when the system is quiescent. *)
FinishIffTerminated == finished <=> Terminated

(* Safety: terminals are never pruned and the active subgraph stays connected. *)
ConnectivityInv ==
    /\ Terminals \subseteq active
    /\ Connected(active)

(* No conflicting simultaneous deactivations: two adjacent nodes cannot  *)
(* both be gone with each still counted active by the other.             *)
NoConflictInv ==
    \A n \in Nodes \ active :
        \A m \in Nbr(n) \ active : ~ (n \in known[m] /\ m \in known[n])

-----------------------------------------------------------------------------
(* Liveness: the protocol eventually reaches a stable configuration in    *)
(* which no further deactivations occur, and it stays there.              *)
Liveness == <>[]finished

THEOREM Spec => [](TypeOK /\ NeighborInv /\ FinishIffTerminated
                   /\ ConnectivityInv /\ NoConflictInv)
THEOREM Spec => Liveness
=============================================================================