---------------------------- MODULE YoYoNoPruning ----------------------------
(***************************************************************************)
(* Yo-Yo leader election on an arbitrary connected undirected graph,      *)
(* without pruning.                                                        *)
(*                                                                         *)
(* Edges are initially oriented from the smaller identifier to the        *)
(* larger one. Each round has two phases:                                  *)
(*   - "down": sources send their own identifier along outgoing edges.    *)
(*     Every other node waits for values from all incoming neighbors and  *)
(*     forwards the minimum along its outgoing edges.                      *)
(*   - "up": sinks answer "yes" to the senders of the minimum value and   *)
(*     "no" to all other senders. Internal nodes wait for answers from    *)
(*     all outgoing neighbors. If every answer is "yes", they answer      *)
(*     "yes" to the senders of the minimum value and "no" to the others.  *)
(*     Otherwise they answer "no" to everyone.                             *)
(* Every edge along which a "no" travels is reversed. Eventually the node *)
(* with the minimum identifier is the only source, and it is the leader. *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges

ASSUME Nodes \subseteq Nat /\ Nodes # {}
ASSUME Edges \subseteq {{m, n} : m, n \in Nodes}
ASSUME \A e \in Edges : Cardinality(e) = 2

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}
Min(S) == CHOOSE x \in S : \A y \in S : x <= y
MinNode == Min(Nodes)

VARIABLES phase, incoming, outgoing, mailbox
vars == <<phase, incoming, outgoing, mailbox>>

DownMsg(s, v) == [phase |-> "down", sndr |-> s, val |-> v]
UpMsg(s, r)   == [phase |-> "up", sndr |-> s, reply |-> r]

Messages ==
    [phase : {"down"}, sndr : Nodes, val : Nodes]
    \cup [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}]

kind(n) ==
    IF incoming[n] = {} THEN "source"
    ELSE IF outgoing[n] = {} THEN "sink"
    ELSE "internal"

isLeader(n) == kind(n) = "source"

-----------------------------------------------------------------------------
TypeOK ==
    /\ phase \in [Nodes -> {"down", "up"}]
    /\ incoming \in [Nodes -> SUBSET Nodes]
    /\ outgoing \in [Nodes -> SUBSET Nodes]
    /\ mailbox \in [Nodes -> SUBSET Messages]
    /\ \A n \in Nodes : \A msg \in mailbox[n] : msg.sndr \in Neighbors(n)

Init ==
    /\ phase = [n \in Nodes |-> "down"]
    /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
    /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
    /\ mailbox = [n \in Nodes |-> {}]

-----------------------------------------------------------------------------
(* Down phase at a source: send own identifier along outgoing edges. *)
DownSource(n) ==
    /\ phase[n] = "down"
    /\ incoming[n] = {}
    /\ mailbox' = [m \in Nodes |->
                     IF m \in outgoing[n]
                     THEN mailbox[m] \cup {DownMsg(n, n)}
                     ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<incoming, outgoing>>

(* Down phase at a non-source: wait for all incoming values, then forward the minimum. *)
DownOther(n) ==
    /\ phase[n] = "down"
    /\ incoming[n] # {}
    /\ LET dms == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
           mn  == Min({msg.val : msg \in dms})
       IN  /\ {msg.sndr : msg \in dms} = incoming[n]
           /\ mailbox' = [m \in Nodes |->
                            IF m \in outgoing[n]
                            THEN mailbox[m] \cup {DownMsg(n, mn)}
                            ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<incoming, outgoing>>

(* Up phase: wait for answers from all outgoing neighbors, answer the
   incoming neighbors, and reverse every edge along which "no" travels. *)
Up(n) ==
    /\ phase[n] = "up"
    /\ LET ums    == {msg \in mailbox[n] : msg.phase = "up" /\ msg.sndr \in outgoing[n]}
           dms    == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
           mn     == Min({msg.val : msg \in dms})
           allYes == \A u \in ums : u.reply = "yes"
           yesIn  == IF allYes
                     THEN {d.sndr : d \in {x \in dms : x.val = mn}}
                     ELSE {}
           noIn   == incoming[n] \ yesIn
           noOut  == {u.sndr : u \in {x \in ums : x.reply = "no"}}
       IN  /\ {u.sndr : u \in ums} = outgoing[n]
           /\ {d.sndr : d \in dms} = incoming[n]
           /\ mailbox' = [m \in Nodes |->
                            IF m = n THEN mailbox[n] \ (ums \cup dms)
                            ELSE IF m \in yesIn THEN mailbox[m] \cup {UpMsg(n, "yes")}
                            ELSE IF m \in noIn THEN mailbox[m] \cup {UpMsg(n, "no")}
                            ELSE mailbox[m]]
           /\ incoming' = [incoming EXCEPT ![n] = (@ \ noIn) \cup noOut]
           /\ outgoing' = [outgoing EXCEPT ![n] = (@ \ noOut) \cup noIn]
    /\ phase' = [phase EXCEPT ![n] = "down"]

Step(n) == DownSource(n) \/ DownOther(n) \/ Up(n)

Next == \E n \in Nodes : Step(n)

Spec == Init /\ [][Next]_vars /\ \A n \in Nodes : WF_vars(Step(n))

-----------------------------------------------------------------------------
(* The orientations of edges are consistent between neighbors, except
   while a "no" answer that reverses the edge is still in transit. *)
NeighborInv ==
    \A n \in Nodes :
        /\ incoming[n] \cap outgoing[n] = {}
        /\ incoming[n] \cup outgoing[n] = Neighbors(n)
        /\ \A m \in incoming[n] : n \in outgoing[m]
        /\ \A m \in outgoing[n] :
              n \in outgoing[m] =>
                 \/ UpMsg(m, "no") \in mailbox[n]
                 \/ UpMsg(n, "no") \in mailbox[m]

(* No new sources appear. The initial sources are exactly the local minima,
   so every source is still a local minimum. *)
NoNewSource ==
    \A n \in Nodes : kind(n) = "source" => \A m \in Neighbors(n) : n < m

(* At most one leader, and it is the minimum node, once election completes. *)
LeaderInv ==
    \A n \in Nodes : isLeader(n) /\ (\A m \in Nodes \ {n} : ~ isLeader(m)) => n = MinNode

(* Eventually the minimum node is the unique source (leader), and everyone else knows it is not. *)
Liveness ==
    <>[](\A n \in Nodes : (kind(n) = "source") <=> (n = MinNode))

=============================================================================