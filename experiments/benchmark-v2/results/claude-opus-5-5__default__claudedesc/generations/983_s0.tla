---------------------------- MODULE MCYoYoPruning ----------------------------
(***************************************************************************)
(* Model-checking configuration for the Yo-Yo leader election algorithm   *)
(* with pruning on an undirected graph. The algorithm is stated inline so  *)
(* the module is self-contained. Deadlock checking is disabled in the      *)
(* model: the terminal state, where a leader has been elected, has no      *)
(* successor.                                                              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* Concrete graph topology: 5 nodes, 5 edges.                              *)
(***************************************************************************)
Nodes == 1 .. 5
Edges == { {1,2}, {1,3}, {2,3}, {3,4}, {4,5} }

(***************************************************************************)
(* Larger alternative configuration: 11 nodes, 14 edges.                   *)
(*                                                                         *)
(* Nodes == 1 .. 11                                                        *)
(* Edges == { {1,2}, {1,3}, {2,4}, {3,4}, {4,5}, {5,6}, {5,7}, {6,8},      *)
(*            {7,8}, {8,9}, {9,10}, {9,11}, {10,11}, {2,6} }               *)
(***************************************************************************)

VARIABLES active, phase, incoming, outgoing, mailbox

vars == <<active, phase, incoming, outgoing, mailbox>>

Neighbors(n) == { m \in Nodes : {m, n} \in Edges }

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Messages ==
    [phase : {"down"}, sndr : Nodes, val : Nodes]
    \cup
    [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}, prune : BOOLEAN]

-----------------------------------------------------------------------------
TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ phase \in [Nodes -> {"down", "up"}]
    /\ incoming \in [Nodes -> SUBSET Nodes]
    /\ outgoing \in [Nodes -> SUBSET Nodes]
    /\ mailbox \in [Nodes -> SUBSET Messages]
    /\ \A n \in Nodes : incoming[n] \cup outgoing[n] \subseteq Neighbors(n)
    /\ \A n \in Nodes : incoming[n] \cap outgoing[n] = {}

-----------------------------------------------------------------------------
(* Initially, edges are oriented from smaller to larger node identity. *)
Init ==
    /\ active = [n \in Nodes |-> TRUE]
    /\ phase = [n \in Nodes |-> "down"]
    /\ incoming = [n \in Nodes |-> { m \in Neighbors(n) : m < n }]
    /\ outgoing = [n \in Nodes |-> { m \in Neighbors(n) : m > n }]
    /\ mailbox = [n \in Nodes |-> {}]

(* Down phase at a source: send own identity to all outgoing neighbors. *)
DownSource(n) ==
    /\ active[n]
    /\ phase[n] = "down"
    /\ incoming[n] = {}
    /\ outgoing[n] # {}
    /\ mailbox' = [m \in Nodes |->
                     IF m \in outgoing[n]
                     THEN mailbox[m] \cup {[phase |-> "down", sndr |-> n, val |-> n]}
                     ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<active, incoming, outgoing>>

(* Down phase at an internal node or sink: once values have arrived from  *)
(* all incoming neighbors, forward the minimum to all outgoing neighbors.  *)
DownOther(n) ==
    /\ active[n]
    /\ phase[n] = "down"
    /\ incoming[n] # {}
    /\ LET dm == { x \in mailbox[n] : x.phase = "down" /\ x.sndr \in incoming[n] }
       IN  /\ { x.sndr : x \in dm } = incoming[n]
           /\ mailbox' = [m \in Nodes |->
                            IF m \in outgoing[n]
                            THEN mailbox[m] \cup
                                   {[phase |-> "down", sndr |-> n,
                                     val |-> Min({ x.val : x \in dm })]}
                            ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<active, incoming, outgoing>>

(* Up phase at a source: collect replies from all outgoing neighbors, flip *)
(* edges for "no" replies and remove pruned edges.                         *)
UpSource(n) ==
    /\ active[n]
    /\ phase[n] = "up"
    /\ incoming[n] = {}
    /\ LET um == { x \in mailbox[n] : x.phase = "up" /\ x.sndr \in outgoing[n] }
           no == { x.sndr : x \in { y \in um : y.reply = "no" } }
           pr == { x.sndr : x \in { y \in um : y.prune } }
       IN  /\ { x.sndr : x \in um } = outgoing[n]
           /\ mailbox' = [mailbox EXCEPT ![n] = @ \ um]
           /\ incoming' = [incoming EXCEPT ![n] = no \ pr]
           /\ outgoing' = [outgoing EXCEPT ![n] = (outgoing[n] \ no) \ pr]
    /\ phase' = [phase EXCEPT ![n] = "down"]
    /\ UNCHANGED active

(* Up phase at an internal node or sink. The node answers "yes" to the     *)
(* senders of the minimum value if all outgoing neighbors said "yes", and  *)
(* "no" to everyone else. Pruning works as follows. A node that has become *)
(* a sink and received a single value prunes itself and becomes inactive.  *)
(* Otherwise it keeps only one incoming link per received value.           *)
UpOther(n) ==
    /\ active[n]
    /\ phase[n] = "up"
    /\ incoming[n] # {}
    /\ LET dm == { x \in mailbox[n] : x.phase = "down" /\ x.sndr \in incoming[n] }
           um == { x \in mailbox[n] : x.phase = "up" /\ x.sndr \in outgoing[n] }
           no == { x.sndr : x \in { y \in um : y.reply = "no" } }
           prOut == { x.sndr : x \in { y \in um : y.prune } }
           vals == { x.val : x \in dm }
           minVal == Min(vals)
           yesTo == IF no = {}
                    THEN { x.sndr : x \in { y \in dm : y.val = minVal } }
                    ELSE {}
           noTo == incoming[n] \ yesTo
           valOf(s) == (CHOOSE x \in dm : x.sndr = s).val
           keep(s) == s = Min({ x.sndr : x \in { y \in dm : y.val = valOf(s) } })
           prunable == (outgoing[n] \ prOut = {}) /\ Cardinality(vals) = 1
           prIn == IF prunable THEN incoming[n]
                   ELSE { s \in incoming[n] : ~ keep(s) }
       IN  /\ { x.sndr : x \in um } = outgoing[n]
           /\ mailbox' = [m \in Nodes |->
                            IF m = n THEN mailbox[n] \ (dm \cup um)
                            ELSE IF m \in incoming[n]
                            THEN mailbox[m] \cup
                                   {[phase |-> "up", sndr |-> n,
                                     reply |-> IF m \in yesTo THEN "yes" ELSE "no",
                                     prune |-> m \in prIn]}
                            ELSE mailbox[m]]
           /\ active' = [active EXCEPT ![n] = ~ prunable]
           /\ incoming' = [incoming EXCEPT ![n] =
                             IF prunable THEN {}
                             ELSE (yesTo \ prIn) \cup (no \ prOut)]
           /\ outgoing' = [outgoing EXCEPT ![n] =
                             IF prunable THEN {}
                             ELSE (noTo \ prIn) \cup ((outgoing[n] \ no) \ prOut)]
    /\ phase' = [phase EXCEPT ![n] = "down"]

Next ==
    \E n \in Nodes :
        \/ DownSource(n)
        \/ DownOther(n)
        \/ UpSource(n)
        \/ UpOther(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

(* Neighbor views are consistent unless an "up" message is still pending  *)
(* on the edge, which means one endpoint has updated before the other.     *)
NeighborInv ==
    \A m, n \in Nodes :
        \/ (m \in outgoing[n] <=> n \in incoming[m])
        \/ \E x \in mailbox[n] \cup mailbox[m] :
              x.phase = "up" /\ x.sndr \in {m, n}

(* The algorithm has finished when no active node has any remaining edge. *)
Finished ==
    \A n \in Nodes : active[n] => (incoming[n] = {} /\ outgoing[n] = {})

FinishIffTerminated == Finished <=> ~ ENABLED Next

Liveness == <>Finished

(***************************************************************************)
(* The following property fails for the small example graph:              *)
(*                                                                         *)
(* NoNewSource ==                                                          *)
(*     [][\A n \in Nodes :                                                 *)
(*          (active'[n] /\ incoming'[n] = {} /\ outgoing'[n] # {})         *)
(*             => incoming[n] = {}]_vars                                   *)
(***************************************************************************)

(***************************************************************************)
(* Model configuration (cfg):                                              *)
(*   SPECIFICATION Spec                                                    *)
(*   INVARIANTS TypeOK NeighborInv FinishIffTerminated                     *)
(*   PROPERTIES Liveness                                                   *)
(*   CHECK_DEADLOCK FALSE                                                  *)
(***************************************************************************)
=============================================================================