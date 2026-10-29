---------------------------- MODULE YoYoPruning ----------------------------
(***************************************************************************)
(* Yo-Yo leader election with pruning on undirected, loop-free, connected *)
(* graphs over a fixed finite set of numbered nodes.                      *)
(*                                                                         *)
(* The initial state nondeterministically chooses a connected graph over  *)
(* Nodes and orients every edge from the smaller to the larger endpoint.  *)
(* The algorithm then alternates between down and up phases:             *)
(*  - Down phase: sources send their identity to their out-neighbors.     *)
(*    Internal nodes and sinks wait for values from all in-neighbors.     *)
(*    Internal nodes then forward the minimum value to their              *)
(*    out-neighbors.                                                      *)
(*  - Up phase: sinks and internal nodes wait for replies from all        *)
(*    out-neighbors. They then answer "yes" to in-neighbors that sent the *)
(*    minimum value, or "no" to all in-neighbors if some out-neighbor     *)
(*    answered "no". Edges carrying a "no" are reversed.                  *)
(*  - Pruning: a node that receives the same value from several           *)
(*    in-neighbors keeps only one of those edges. A sink with a single    *)
(*    remaining in-neighbor removes itself and becomes inactive.          *)
(* Eventually only the leader (the minimum node) remains active, as an    *)
(* isolated source.                                                       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT Nodes
ASSUME /\ Nodes \subseteq Nat
       /\ Nodes # {}
       /\ IsFiniteSet(Nodes)

VARIABLES
    active,    \* active[n]: is node n still active?
    phase,     \* phase[n] \in {"down", "up"}
    incoming,  \* incoming[n]: current in-neighbors of n
    outgoing,  \* outgoing[n]: current out-neighbors of n
    mailbox    \* mailbox[n]: set of messages received by n

vars == <<active, phase, incoming, outgoing, mailbox>>

-----------------------------------------------------------------------------
(* Auxiliary definitions *)

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

PossibleEdges == {e \in SUBSET Nodes : Cardinality(e) = 2}

RECURSIVE Reach(_, _)
Reach(S, E) ==
    LET T == S \cup {m \in Nodes : \E n \in S : {m, n} \in E}
    IN  IF T = S THEN S ELSE Reach(T, E)

IsConnected(E) == \A n \in Nodes : Reach({n}, E) = Nodes

(* Messages have a uniform record shape. *)
DownMsg(s, v) ==
    [phs |-> "down", sndr |-> s, val |-> v, reply |-> "none", prune |-> FALSE]
UpMsg(s, r, p) ==
    [phs |-> "up", sndr |-> s, val |-> s, reply |-> r, prune |-> p]

Messages ==
    {DownMsg(s, v) : s \in Nodes, v \in Nodes}
    \cup {UpMsg(s, r, p) : s \in Nodes, r \in {"yes", "no"}, p \in BOOLEAN}

HasDownFrom(n, m) == \E msg \in mailbox[n] : msg.phs = "down" /\ msg.sndr = m
HasUpFrom(n, k)   == \E msg \in mailbox[n] : msg.phs = "up" /\ msg.sndr = k

DownVal(n, m) ==
    (CHOOSE msg \in mailbox[n] : msg.phs = "down" /\ msg.sndr = m).val
UpReply(n, k) ==
    CHOOSE msg \in mailbox[n] : msg.phs = "up" /\ msg.sndr = k

ReceivedAllDown(n) == \A m \in incoming[n] : HasDownFrom(n, m)
ReceivedAllUp(n)   == \A k \in outgoing[n] : HasUpFrom(n, k)

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ \E E \in SUBSET PossibleEdges :
          /\ IsConnected(E)
          /\ incoming = [n \in Nodes |-> {m \in Nodes : {m, n} \in E /\ m < n}]
          /\ outgoing = [n \in Nodes |-> {m \in Nodes : {m, n} \in E /\ n < m}]
    /\ active  = [n \in Nodes |-> TRUE]
    /\ phase   = [n \in Nodes |-> "down"]
    /\ mailbox = [n \in Nodes |-> {}]

-----------------------------------------------------------------------------
(* Down phase *)

(* A source sends its own identity to all its out-neighbors. *)
DownSource(n) ==
    /\ active[n]
    /\ phase[n] = "down"
    /\ incoming[n] = {}
    /\ outgoing[n] # {}
    /\ mailbox' = [m \in Nodes |->
                     IF m \in outgoing[n]
                     THEN mailbox[m] \cup {DownMsg(n, n)}
                     ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<active, incoming, outgoing>>

(* An internal node or sink waits for values from all in-neighbors. *)
(* It then forwards their minimum to its out-neighbors, if any.     *)
DownOther(n) ==
    /\ active[n]
    /\ phase[n] = "down"
    /\ incoming[n] # {}
    /\ ReceivedAllDown(n)
    /\ LET minVal == Min({DownVal(n, m) : m \in incoming[n]})
       IN  mailbox' = [m \in Nodes |->
                         IF m \in outgoing[n]
                         THEN mailbox[m] \cup {DownMsg(n, minVal)}
                         ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<active, incoming, outgoing>>

-----------------------------------------------------------------------------
(* Up phase *)

(* A source collects the replies from all its out-neighbors.          *)
(* It removes pruned edges and reverses edges answered with "no".     *)
UpSource(n) ==
    /\ active[n]
    /\ phase[n] = "up"
    /\ incoming[n] = {}
    /\ ReceivedAllUp(n)
    /\ LET prunedOut  == {k \in outgoing[n] : UpReply(n, k).prune}
           flippedOut == {k \in outgoing[n] \ prunedOut :
                             UpReply(n, k).reply = "no"}
       IN  /\ outgoing' = [outgoing EXCEPT ![n] = @ \ (prunedOut \cup flippedOut)]
           /\ incoming' = [incoming EXCEPT ![n] = flippedOut]
    /\ mailbox' = [mailbox EXCEPT ![n] = {msg \in @ : msg.phs = "down"}]
    /\ phase' = [phase EXCEPT ![n] = "down"]
    /\ UNCHANGED active

(* An internal node or sink collects the replies from all its            *)
(* out-neighbors and replies to its in-neighbors. While doing so, it     *)
(* prunes duplicate in-edges and, if it is a sink with a single          *)
(* remaining in-neighbor, removes itself.                                *)
UpOther(n) ==
    /\ active[n]
    /\ phase[n] = "up"
    /\ incoming[n] # {}
    /\ ReceivedAllUp(n)
    /\ LET vals       == [m \in incoming[n] |-> DownVal(n, m)]
           minVal     == Min({vals[m] : m \in incoming[n]})
           prunedOut  == {k \in outgoing[n] : UpReply(n, k).prune}
           flippedOut == {k \in outgoing[n] \ prunedOut :
                             UpReply(n, k).reply = "no"}
           anyNo      == \E k \in outgoing[n] : UpReply(n, k).reply = "no"
           \* one representative (smallest id) per received value
           keep       == {m \in incoming[n] :
                             \A m2 \in incoming[n] : vals[m2] = vals[m] => m <= m2}
           selfPrune  == outgoing[n] = {} /\ Cardinality(keep) = 1
           reply(m)   == IF ~anyNo /\ vals[m] = minVal THEN "yes" ELSE "no"
           prune(m)   == (m \notin keep) \/ selfPrune
           flippedIn  == {m \in keep : reply(m) = "no"}
       IN  /\ mailbox' = [x \in Nodes |->
                IF x = n
                THEN {msg \in mailbox[n] :
                         msg.phs = "down" /\ msg.sndr \notin incoming[n]}
                ELSE IF x \in incoming[n]
                     THEN mailbox[x] \cup {UpMsg(n, reply(x), prune(x))}
                     ELSE mailbox[x]]
           /\ IF selfPrune
              THEN /\ active'   = [active EXCEPT ![n] = FALSE]
                   /\ incoming' = [incoming EXCEPT ![n] = {}]
                   /\ outgoing' = [outgoing EXCEPT ![n] = {}]
              ELSE /\ active'   = active
                   /\ incoming' = [incoming EXCEPT ![n] =
                                     (keep \ flippedIn) \cup flippedOut]
                   /\ outgoing' = [outgoing EXCEPT ![n] =
                                     (@ \ (prunedOut \cup flippedOut)) \cup flippedIn]
    /\ phase' = [phase EXCEPT ![n] = "down"]

-----------------------------------------------------------------------------
Next ==
    \E n \in Nodes :
        \/ DownSource(n)
        \/ DownOther(n)
        \/ UpSource(n)
        \/ UpOther(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
    /\ active   \in [Nodes -> BOOLEAN]
    /\ phase    \in [Nodes -> {"down", "up"}]
    /\ incoming \in [Nodes -> SUBSET Nodes]
    /\ outgoing \in [Nodes -> SUBSET Nodes]
    /\ mailbox  \in [Nodes -> SUBSET Messages]

NoSelfLoops ==
    \A n \in Nodes : n \notin incoming[n] \cup outgoing[n]

InOutDisjoint ==
    \A n \in Nodes : incoming[n] \cap outgoing[n] = {}

InactiveIsolated ==
    \A n \in Nodes : ~active[n] => (incoming[n] = {} /\ outgoing[n] = {})

SomeNodeActive == \E n \in Nodes : active[n]

MinNodeActive == active[Min(Nodes)]

(* Termination: every active node is an isolated node in the down phase. *)
Termination ==
    \A n \in Nodes :
        active[n] => /\ incoming[n] = {}
                     /\ outgoing[n] = {}
                     /\ phase[n] = "down"

LeaderIsMin ==
    Termination => \A n \in Nodes : active[n] <=> (n = Min(Nodes))

-----------------------------------------------------------------------------
(* Liveness and termination characterization *)

Liveness == <>Termination

TerminationIffDeadlock == [](Termination <=> ~ENABLED Next)

=============================================================================