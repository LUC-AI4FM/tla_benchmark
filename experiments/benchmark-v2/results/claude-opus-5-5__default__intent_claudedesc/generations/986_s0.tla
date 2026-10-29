---------------------------- MODULE YoYoPruning ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges

ASSUME NodesAssump == Nodes # {} /\ IsFiniteSet(Nodes) /\ Nodes \subseteq Int

ASSUME EdgesAssump ==
    Edges \subseteq {e \in SUBSET Nodes : Cardinality(e) = 2}

IsConnected ==
    \A S \in SUBSET Nodes :
        (S # {} /\ S # Nodes) =>
            \E e \in Edges : e \cap S # {} /\ e \ S # {}

ASSUME ConnectedAssump == IsConnected

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

MinNode == Min(Nodes)

DownMsgs == [phase : {"down"}, sndr : Nodes, val : Nodes]
UpMsgs   == [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}, prune : BOOLEAN]
Messages == DownMsgs \cup UpMsgs

VARIABLES active, phase, incoming, outgoing, mailbox

vars == <<active, phase, incoming, outgoing, mailbox>>

-----------------------------------------------------------------------------
Init ==
    /\ active   = [n \in Nodes |-> TRUE]
    /\ phase    = [n \in Nodes |-> "down"]
    /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
    /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
    /\ mailbox  = [n \in Nodes |-> {}]

-----------------------------------------------------------------------------
(* Down phase of a source: send own identity to all outgoing neighbors. *)
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

(* Down phase of a non-source: wait for values from all incoming neighbors,
   forward the minimum to all outgoing neighbors. *)
DownOther(n) ==
    /\ active[n]
    /\ phase[n] = "down"
    /\ incoming[n] # {}
    /\ LET downMsgs == {msg \in mailbox[n] :
                           msg.phase = "down" /\ msg.sndr \in incoming[n]}
       IN  /\ {msg.sndr : msg \in downMsgs} = incoming[n]
           /\ LET minVal == Min({msg.val : msg \in downMsgs})
              IN  mailbox' = [m \in Nodes |->
                       IF m \in outgoing[n]
                       THEN mailbox[m] \cup {[phase |-> "down", sndr |-> n, val |-> minVal]}
                       ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<active, incoming, outgoing>>

(* Up phase of a source: collect replies from all outgoing neighbors,
   reverse edges for "no" replies and remove pruned edges. *)
UpSource(n) ==
    /\ active[n]
    /\ phase[n] = "up"
    /\ incoming[n] = {}
    /\ LET upMsgs == {msg \in mailbox[n] :
                         msg.phase = "up" /\ msg.sndr \in outgoing[n]}
       IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
           /\ LET noSndrs == {msg.sndr : msg \in {x \in upMsgs : x.reply = "no"}}
                  pruned  == {msg.sndr : msg \in {x \in upMsgs : x.prune}}
              IN  /\ outgoing' = [outgoing EXCEPT ![n] = outgoing[n] \ (noSndrs \cup pruned)]
                  /\ incoming' = [incoming EXCEPT ![n] = noSndrs \ pruned]
                  /\ mailbox'  = [mailbox EXCEPT ![n] = mailbox[n] \ upMsgs]
    /\ phase' = [phase EXCEPT ![n] = "down"]
    /\ UNCHANGED active

(* Up phase of a non-source (internal node or sink): collect replies from all
   outgoing neighbors, reply to incoming neighbors, and apply pruning. *)
UpOther(n) ==
    /\ active[n]
    /\ phase[n] = "up"
    /\ incoming[n] # {}
    /\ LET upMsgs   == {msg \in mailbox[n] :
                           msg.phase = "up" /\ msg.sndr \in outgoing[n]}
           downMsgs == {msg \in mailbox[n] :
                           msg.phase = "down" /\ msg.sndr \in incoming[n]}
       IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
           /\ LET noSndrs  == {msg.sndr : msg \in {x \in upMsgs : x.reply = "no"}}
                  pruned   == {msg.sndr : msg \in {x \in upMsgs : x.prune}}
                  minVal   == Min({msg.val : msg \in downMsgs})
                  minSndrs == {msg.sndr : msg \in {x \in downMsgs : x.val = minVal}}
                  sinkPrune == /\ outgoing[n] \subseteq pruned
                               /\ minSndrs = incoming[n]
              IN  \E k \in minSndrs :
                    LET Reply(m) == IF noSndrs # {} THEN "no"
                                    ELSE IF m \in minSndrs THEN "yes" ELSE "no"
                        Prune(m) == sinkPrune \/ (m \in minSndrs /\ m # k)
                        revIn  == {m \in incoming[n] : Reply(m) = "no" /\ ~Prune(m)}
                        keepIn == {m \in incoming[n] : Reply(m) = "yes" /\ ~Prune(m)}
                    IN  /\ incoming' = [incoming EXCEPT ![n] =
                                          IF sinkPrune THEN {}
                                          ELSE keepIn \cup (noSndrs \ pruned)]
                        /\ outgoing' = [outgoing EXCEPT ![n] =
                                          IF sinkPrune THEN {}
                                          ELSE (outgoing[n] \ (noSndrs \cup pruned)) \cup revIn]
                        /\ active' = IF sinkPrune
                                     THEN [active EXCEPT ![n] = FALSE]
                                     ELSE active
                        /\ mailbox' = [m \in Nodes |->
                               IF m = n THEN mailbox[n] \ (upMsgs \cup downMsgs)
                               ELSE IF m \in incoming[n]
                                    THEN mailbox[m] \cup
                                           {[phase |-> "up", sndr |-> n,
                                             reply |-> Reply(m), prune |-> Prune(m)]}
                                    ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "down"]

Next ==
    \E n \in Nodes :
        \/ DownSource(n)
        \/ DownOther(n)
        \/ UpSource(n)
        \/ UpOther(n)

Fairness ==
    \A n \in Nodes :
        /\ WF_vars(DownSource(n))
        /\ WF_vars(DownOther(n))
        /\ WF_vars(UpSource(n))
        /\ WF_vars(UpOther(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ active   \in [Nodes -> BOOLEAN]
    /\ phase    \in [Nodes -> {"down", "up"}]
    /\ incoming \in [Nodes -> SUBSET Nodes]
    /\ outgoing \in [Nodes -> SUBSET Nodes]
    /\ mailbox  \in [Nodes -> SUBSET Messages]
    /\ \A n \in Nodes : incoming[n] \cup outgoing[n] \subseteq Neighbors(n)

GraphConsistency ==
    /\ \A n \in Nodes : incoming[n] \cap outgoing[n] = {}
    /\ \A n \in Nodes : ~active[n] => (incoming[n] = {} /\ outgoing[n] = {})
    /\ \A n, m \in Nodes : n \in incoming[m] => m \in outgoing[n]
    /\ \A n, m \in Nodes :
          (m \in outgoing[n] /\ n \notin incoming[m]) =>
             \/ \E msg \in mailbox[n] :
                   /\ msg.phase = "up" /\ msg.sndr = m
                   /\ (msg.reply = "no" \/ msg.prune)
             \/ \E msg \in mailbox[m] :
                   /\ msg.phase = "up" /\ msg.sndr = n
                   /\ msg.reply = "no" /\ ~msg.prune

-----------------------------------------------------------------------------
(* Termination and liveness *)

IsLeader(n) == active[n] /\ incoming[n] = {} /\ outgoing[n] = {}

Finished ==
    /\ \E l \in Nodes :
          /\ IsLeader(l)
          /\ \A n \in Nodes \ {l} : ~active[n]
    /\ \A n \in Nodes : mailbox[n] = {}

UniqueLeaderAtEnd ==
    Finished => \A a, b \in Nodes : (IsLeader(a) /\ IsLeader(b)) => a = b

CorrectLeaderAtEnd == Finished => IsLeader(MinNode)

Termination == <>Finished

CorrectLeader == <>[](Finished /\ IsLeader(MinNode))

CompleteShutdown ==
    <>[](/\ \A n \in Nodes \ {MinNode} : ~active[n]
         /\ \A n \in Nodes : mailbox[n] = {})

TerminationDetection == [](Finished <=> ~ENABLED Next)

=============================================================================