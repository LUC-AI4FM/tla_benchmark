---------------------------- MODULE YoYoPruning ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges

ASSUME /\ Nodes \subseteq Int
       /\ Nodes # {}
       /\ \A e \in Edges : e \subseteq Nodes /\ Cardinality(e) = 2

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Leader == Min(Nodes)

VARIABLES active, phase, incoming, outgoing, mailbox

vars == <<active, phase, incoming, outgoing, mailbox>>

Messages ==
     [phase : {"down"}, sndr : Nodes, val : Nodes]
  \cup [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}, prune : BOOLEAN]

downMsg(s, v) == [phase |-> "down", sndr |-> s, val |-> v]
upMsg(s, r, p) == [phase |-> "up", sndr |-> s, reply |-> r, prune |-> p]

kind(n) ==
  IF incoming[n] = {} THEN "source"
  ELSE IF outgoing[n] = {} THEN "sink"
  ELSE "internal"

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox \in [Nodes -> SUBSET Messages]

NeighborInv ==
  \A n \in Nodes :
     /\ incoming[n] \cup outgoing[n] \subseteq Neighbors(n)
     /\ incoming[n] \cap outgoing[n] = {}
     /\ ~active[n] => incoming[n] = {} /\ outgoing[n] = {}

Init ==
  /\ active = [n \in Nodes |-> TRUE]
  /\ phase = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ mailbox = [n \in Nodes |-> {}]

(* Down phase for a source node: broadcast own identity. *)
DownSource(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] = {}
  /\ outgoing[n] # {}
  /\ mailbox' = [m \in Nodes |->
                   IF m \in outgoing[n] THEN mailbox[m] \cup {downMsg(n, n)}
                   ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

(* Down phase for a non-source node: forward the minimum received value. *)
DownOther(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] # {}
  /\ LET downMsgs == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
     IN  /\ {msg.sndr : msg \in downMsgs} = incoming[n]
         /\ LET mv == Min({msg.val : msg \in downMsgs})
            IN  mailbox' = [m \in Nodes |->
                              IF m \in outgoing[n] THEN mailbox[m] \cup {downMsg(n, mv)}
                              ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

(* Up phase for a source node: collect replies, reorient and prune edges. *)
UpSource(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ incoming[n] = {}
  /\ LET upMsgs == {msg \in mailbox[n] : msg.phase = "up" /\ msg.sndr \in outgoing[n]}
         replyOf(k) == CHOOSE msg \in upMsgs : msg.sndr = k
         prunedOut == {k \in outgoing[n] : replyOf(k).prune}
         remOut == outgoing[n] \ prunedOut
         noOut == {k \in remOut : replyOf(k).reply = "no"}
         yesOut == remOut \ noOut
     IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
         /\ incoming' = [incoming EXCEPT ![n] = noOut]
         /\ outgoing' = [outgoing EXCEPT ![n] = yesOut]
         /\ mailbox' = [mailbox EXCEPT ![n] = mailbox[n] \ upMsgs]
  /\ phase' = [phase EXCEPT ![n] = "down"]
  /\ UNCHANGED active

(* Up phase for a non-source node: reply to in-neighbors, prune, reorient. *)
UpOther(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ incoming[n] # {}
  /\ LET upMsgs == {msg \in mailbox[n] : msg.phase = "up" /\ msg.sndr \in outgoing[n]}
         downMsgs == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
         replyOf(k) == CHOOSE msg \in upMsgs : msg.sndr = k
         senderVal(m) == (CHOOSE msg \in downMsgs : msg.sndr = m).val
         prunedOut == {k \in outgoing[n] : replyOf(k).prune}
         remOut == outgoing[n] \ prunedOut
         allYes == \A k \in remOut : replyOf(k).reply = "yes"
         noOut == {k \in remOut : replyOf(k).reply = "no"}
         yesOut == remOut \ noOut
         vals == {senderVal(m) : m \in incoming[n]}
         minv == Min(vals)
         keep(m) == m = Min({p \in incoming[n] : senderVal(p) = senderVal(m)})
         leaf == remOut = {} /\ Cardinality(vals) = 1
         rep(m) == IF allYes /\ senderVal(m) = minv THEN "yes" ELSE "no"
         prn(m) == leaf \/ ~keep(m)
         newIn == {m \in incoming[n] : ~prn(m) /\ rep(m) = "yes"} \cup noOut
         newOut == {m \in incoming[n] : ~prn(m) /\ rep(m) = "no"} \cup yesOut
     IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
         /\ {msg.sndr : msg \in downMsgs} = incoming[n]
         /\ mailbox' = [x \in Nodes |->
                          IF x = n THEN mailbox[n] \ (upMsgs \cup downMsgs)
                          ELSE IF x \in incoming[n]
                               THEN mailbox[x] \cup {upMsg(n, rep(x), prn(x))}
                               ELSE mailbox[x]]
         /\ incoming' = [incoming EXCEPT ![n] = IF leaf THEN {} ELSE newIn]
         /\ outgoing' = [outgoing EXCEPT ![n] = IF leaf THEN {} ELSE newOut]
         /\ active' = [active EXCEPT ![n] = ~leaf]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Next ==
  \E n \in Nodes : DownSource(n) \/ DownOther(n) \/ UpSource(n) \/ UpOther(n)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A n \in Nodes :
        /\ WF_vars(DownSource(n))
        /\ WF_vars(DownOther(n))
        /\ WF_vars(UpSource(n))
        /\ WF_vars(UpOther(n))

Terminated ==
  /\ \A n \in Nodes : active[n] <=> n = Leader
  /\ incoming[Leader] = {}
  /\ outgoing[Leader] = {}

Liveness == <>Terminated

FinishIffTerminated == [](~(ENABLED Next) <=> Terminated)

NoNewSource ==
  [][\A n \in Nodes :
        (active'[n] /\ kind(n)' = "source") => kind(n) = "source"]_vars

MoreThanOneSource ==
  \E s1, s2 \in Nodes :
     /\ s1 # s2
     /\ active[s1] /\ active[s2]
     /\ kind(s1) = "source" /\ kind(s2) = "source"

=============================================================================