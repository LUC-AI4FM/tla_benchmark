------------------------------ MODULE YoYoPruning ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Nodes

ASSUME NodesAssump == /\ Nodes \subseteq Nat
                      /\ Nodes # {}
                      /\ IsFiniteSet(Nodes)

VARIABLES active,    \* active[n]: is node n still participating?
          phase,     \* phase[n] \in {"down", "up"}
          incoming,  \* incoming[n]: neighbors with an edge oriented towards n
          outgoing,  \* outgoing[n]: neighbors with an edge oriented away from n
          mailbox    \* mailbox[n]: set of messages received by n

vars == <<active, phase, incoming, outgoing, mailbox>>

-----------------------------------------------------------------------------
(* Auxiliary definitions *)

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

PossibleEdges == {{m, n} : m, n \in Nodes} \ {{n} : n \in Nodes}

Reachable(E, n) ==
    LET R[k \in 0 .. Cardinality(Nodes)] ==
          IF k = 0 THEN {n}
          ELSE R[k-1] \cup {m \in Nodes : \E p \in R[k-1] : {m, p} \in E}
    IN  R[Cardinality(Nodes)]

IsConnected(E) == \A n \in Nodes : Reachable(E, n) = Nodes

Neighbors(n) == incoming[n] \cup outgoing[n]

Messages ==
    [phase : {"down"}, sndr : Nodes, val : Nodes, reply : {"none"}, prune : {FALSE}]
    \cup
    [phase : {"up"}, sndr : Nodes, val : {0}, reply : {"yes", "no"}, prune : BOOLEAN]

DownMsg(s, v) ==
    [phase |-> "down", sndr |-> s, val |-> v, reply |-> "none", prune |-> FALSE]

UpMsg(s, r, p) ==
    [phase |-> "up", sndr |-> s, val |-> 0, reply |-> r, prune |-> p]

DownMsgs(n) == {msg \in mailbox[n] : msg.phase = "down"}
UpMsgs(n)   == {msg \in mailbox[n] : msg.phase = "up"}

-----------------------------------------------------------------------------
(* Initial state: a connected graph, edges oriented from smaller to larger *)

Init ==
    \E E \in SUBSET PossibleEdges :
        /\ IsConnected(E)
        /\ active   = [n \in Nodes |-> TRUE]
        /\ phase    = [n \in Nodes |-> "down"]
        /\ incoming = [n \in Nodes |-> {m \in Nodes : {m, n} \in E /\ m < n}]
        /\ outgoing = [n \in Nodes |-> {m \in Nodes : {m, n} \in E /\ n < m}]
        /\ mailbox  = [n \in Nodes |-> {}]

-----------------------------------------------------------------------------
(* Down phase *)

\* A source sends its own identity to all outgoing neighbors.
DownSource(n) ==
    /\ active[n]
    /\ phase[n] = "down"
    /\ incoming[n] = {}
    /\ outgoing[n] # {}
    /\ mailbox' = [m \in Nodes |->
                     IF m \in outgoing[n] THEN mailbox[m] \cup {DownMsg(n, n)}
                     ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<active, incoming, outgoing>>

\* A non-source node waits for values from all incoming neighbors and
\* forwards the minimum to all outgoing neighbors.
DownOther(n) ==
    /\ active[n]
    /\ phase[n] = "down"
    /\ incoming[n] # {}
    /\ {msg.sndr : msg \in DownMsgs(n)} = incoming[n]
    /\ LET minVal == Min({msg.val : msg \in DownMsgs(n)})
       IN  mailbox' = [m \in Nodes |->
                         IF m \in outgoing[n] THEN mailbox[m] \cup {DownMsg(n, minVal)}
                         ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<active, incoming, outgoing>>

-----------------------------------------------------------------------------
(* Up phase *)

\* A source collects the replies of its outgoing neighbors, reverses edges
\* on which it received "no" and removes edges that were pruned.
UpSource(n) ==
    /\ active[n]
    /\ phase[n] = "up"
    /\ incoming[n] = {}
    /\ {msg.sndr : msg \in UpMsgs(n)} = outgoing[n]
    /\ LET noSndrs   == {msg.sndr : msg \in {u \in UpMsgs(n) : u.reply = "no"}}
           prunedOut == {msg.sndr : msg \in {u \in UpMsgs(n) : u.prune}}
       IN  /\ incoming' = [incoming EXCEPT ![n] = noSndrs \ prunedOut]
           /\ outgoing' = [outgoing EXCEPT ![n] = outgoing[n] \ (noSndrs \cup prunedOut)]
    /\ mailbox' = [mailbox EXCEPT ![n] = mailbox[n] \ UpMsgs(n)]
    /\ phase' = [phase EXCEPT ![n] = "down"]
    /\ UNCHANGED active

\* A non-source node (internal or sink) collects the replies of its outgoing
\* neighbors, then replies to its incoming neighbors, possibly asking for
\* pruning of edges, reverses edges and possibly deactivates itself.
UpOther(n) ==
    /\ active[n]
    /\ phase[n] = "up"
    /\ incoming[n] # {}
    /\ {msg.sndr : msg \in UpMsgs(n)} = outgoing[n]
    /\ LET downMsgs  == DownMsgs(n)
           upMsgs    == UpMsgs(n)
           vals      == {msg.val : msg \in downMsgs}
           minVal    == Min(vals)
           noSndrs   == {msg.sndr : msg \in {u \in upMsgs : u.reply = "no"}}
           prunedOut == {msg.sndr : msg \in {u \in upMsgs : u.prune}}
           isSink    == outgoing[n] = {}
           valOf(m)  == (CHOOSE d \in downMsgs : d.sndr = m).val
           rep(v)    == Min({d.sndr : d \in {dd \in downMsgs : dd.val = v}})
           pruneSelf == isSink /\ Cardinality(vals) = 1
           toPrune   == {m \in incoming[n] : rep(valOf(m)) # m \/ pruneSelf}
           replyTo(m) == IF noSndrs # {} \/ valOf(m) # minVal THEN "no" ELSE "yes"
           noIn      == {m \in incoming[n] : replyTo(m) = "no"}
       IN  /\ mailbox' = [m \in Nodes |->
                            IF m = n THEN mailbox[n] \ (downMsgs \cup upMsgs)
                            ELSE IF m \in incoming[n]
                                 THEN mailbox[m] \cup {UpMsg(n, replyTo(m), m \in toPrune)}
                                 ELSE mailbox[m]]
           /\ incoming' = [incoming EXCEPT ![n] =
                              (incoming[n] \ (toPrune \cup noIn)) \cup (noSndrs \ prunedOut)]
           /\ outgoing' = [outgoing EXCEPT ![n] =
                              (outgoing[n] \ (noSndrs \cup prunedOut)) \cup (noIn \ toPrune)]
           /\ active' = [active EXCEPT ![n] = ~pruneSelf]
    /\ phase' = [phase EXCEPT ![n] = "down"]

-----------------------------------------------------------------------------
Next == \E n \in Nodes :
           \/ DownSource(n)
           \/ DownOther(n)
           \/ UpSource(n)
           \/ UpOther(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
    /\ active   \in [Nodes -> BOOLEAN]
    /\ phase    \in [Nodes -> {"down", "up"}]
    /\ incoming \in [Nodes -> SUBSET Nodes]
    /\ outgoing \in [Nodes -> SUBSET Nodes]
    /\ mailbox  \in [Nodes -> SUBSET Messages]

\* Structural invariants
NoSelfLoops == \A n \in Nodes : n \notin Neighbors(n)

InOutDisjoint == \A n \in Nodes : incoming[n] \cap outgoing[n] = {}

InactiveIsolated == \A n \in Nodes : ~active[n] => Neighbors(n) = {}

EdgesConsistent ==
    \A m, n \in Nodes :
        (active[m] /\ active[n] /\ phase[m] = "down" /\ phase[n] = "down")
        => (m \in outgoing[n] <=> n \in incoming[m])

\* Termination: every remaining active node is isolated and in the down phase
Termination ==
    \A n \in Nodes : active[n] => /\ phase[n] = "down"
                                  /\ incoming[n] = {}
                                  /\ outgoing[n] = {}

\* Upon termination, exactly the node with the smallest identity is active
LeaderElected ==
    Termination => \A n \in Nodes : active[n] <=> n = Min(Nodes)

\* Liveness: the algorithm eventually terminates
Liveness == <>Termination

\* Termination states are exactly the deadlock states
TerminationIffDeadlock == [](Termination <=> ~ENABLED Next)

THEOREM Spec => [](TypeOK /\ NoSelfLoops /\ InOutDisjoint /\ InactiveIsolated
                   /\ EdgesConsistent /\ LeaderElected)
THEOREM Spec => Liveness
THEOREM Spec => TerminationIffDeadlock
=============================================================================