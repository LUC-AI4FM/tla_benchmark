, val : 0 .. N,
   reply : {"yes", "no", "none"}, prune : BOOLEAN]

DownMsg(s, v) ==
  [phase |-> "down", sndr |-> s, val |-> v, reply |-> "none", prune |-> FALSE]

UpMsg(s, r, p) ==
  [phase |-> "up", sndr |-> s, val |-> 0, reply |-> r, prune |-> p]

VARIABLES active, phase, incoming, outgoing, mailbox

vars == <<active, phase, incoming, outgoing, mailbox>>

-----------------------------------------------------------------------------
(* Auxiliary operators *)

DownMsgs(n) ==
  {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}

UpMsgs(n) ==
  {msg \in mailbox[n] : msg.phase = "up" /\ msg.sndr \in outgoing[n]}

ValFrom(n, m) == (CHOOSE msg \in DownMsgs(n) : msg.sndr = m).val

Vals(n) == {msg.val : msg \in DownMsgs(n)}

KeepSets(n) ==
  {K \in SUBSET incoming[n] :
     \A v \in Vals(n) : Cardinality({m \in K : ValFrom(n, m) = v}) = 1}

Reply(n, m, anyNo) ==
  IF anyNo \/ ValFrom(n, m) # Min(Vals(n)) THEN "no" ELSE "yes"

-----------------------------------------------------------------------------
Init ==
  \E E \in SUBSET Pairs :
     /\ Connected(E)
     /\ active = [n \in Nodes |-> TRUE]
     /\ phase = [n \in Nodes |-> "down"]
     /\ incoming = [n \in Nodes |-> {m \in Nbrs(E, n) : m < n}]
     /\ outgoing = [n \in Nodes |-> {m \in Nbrs(E, n) : m > n}]
     /\ mailbox = [n \in Nodes |-> {}]

(* Down phase: a source sends its own identifier *)
DownSource(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] = {}
  /\ outgoing[n] # {}
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ mailbox' = [m \in Nodes |->
                   IF m \in outgoing[n]
                   THEN mailbox[m] \cup {DownMsg(n, n)}
                   ELSE mailbox[m]]
  /\ UNCHANGED <<active, incoming, outgoing>>

(* Down phase: internal node or sink forwards the minimum received value *)
DownOther(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] # {}
  /\ {msg.sndr : msg \in DownMsgs(n)} = incoming[n]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ mailbox' = [m \in Nodes |->
                   IF m \in outgoing[n]
                   THEN mailbox[m] \cup {DownMsg(n, Min(Vals(n)))}
                   ELSE mailbox[m]]
  /\ UNCHANGED <<active, incoming, outgoing>>

(* Up phase: node with incoming links (sink or internal) *)
UpNode(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ incoming[n] # {}
  /\ {msg.sndr : msg \in UpMsgs(n)} = outgoing[n]
  /\ LET ups      == UpMsgs(n)
         noS      == {u.sndr : u \in {x \in ups : x.reply = "no"}}
         prS      == {u.sndr : u \in {x \in ups : x.prune}}
         anyNo    == noS # {}
         remOut   == outgoing[n] \ prS
         consumed == DownMsgs(n) \cup ups
         isLeaf   == remOut = {} /\ Cardinality(Vals(n)) = 1
     IN  \/ /\ isLeaf
            /\ active' = [active EXCEPT ![n] = FALSE]
            /\ incoming' = [incoming EXCEPT ![n] = {}]
            /\ outgoing' = [outgoing EXCEPT ![n] = {}]
            /\ mailbox' = [m \in Nodes |->
                             IF m = n THEN mailbox[n] \ consumed
                             ELSE IF m \in incoming[n]
                                  THEN mailbox[m] \cup {UpMsg(n, Reply(n, m, anyNo), TRUE)}
                                  ELSE mailbox[m]]
            /\ UNCHANGED phase
         \/ /\ ~isLeaf
            /\ \E K \in KeepSets(n) :
                 LET yesK == {m \in K : Reply(n, m, anyNo) = "yes"}
                     noK  == K \ yesK
                 IN  /\ incoming' = [incoming EXCEPT ![n] = yesK \cup (noS \ prS)]
                     /\ outgoing' = [outgoing EXCEPT ![n] = (remOut \ noS) \cup noK]
                     /\ mailbox' = [m \in Nodes |->
                                      IF m = n THEN mailbox[n] \ consumed
                                      ELSE IF m \in incoming[n]
                                           THEN mailbox[m] \cup
                                                  {UpMsg(n, Reply(n, m, anyNo), m \notin K)}
                                           ELSE mailbox[m]]
            /\ phase' = [phase EXCEPT ![n] = "down"]
            /\ UNCHANGED active

(* Up phase: source collects replies, reverses or prunes links *)
UpSource(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ incoming[n] = {}
  /\ {msg.sndr : msg \in UpMsgs(n)} = outgoing[n]
  /\ LET ups == UpMsgs(n)
         noS == {u.sndr : u \in {x \in ups : x.reply = "no"}}
         prS == {u.sndr : u \in {x \in ups : x.prune}}
     IN  /\ incoming' = [incoming EXCEPT ![n] = noS \ prS]
         /\ outgoing' = [outgoing EXCEPT ![n] = outgoing[n] \ (noS \cup prS)]
         /\ mailbox' = [mailbox EXCEPT ![n] = @ \ ups]
  /\ phase' = [phase EXCEPT ![n] = "down"]
  /\ UNCHANGED active

Progress ==
  \E n \in Nodes :
     \/ DownSource(n)
     \/ DownOther(n)
     \/ UpNode(n)
     \/ UpSource(n)

MinNode == 1

Finished ==
  /\ \A n \in Nodes : active[n] <=> n = MinNode
  /\ incoming[MinNode] = {}
  /\ outgoing[MinNode] = {}
  /\ \A n \in Nodes : mailbox[n] = {}

Terminate == Finished /\ UNCHANGED vars

Next == Progress \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Progress)

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox \in [Nodes -> SUBSET Messages]
  /\ \A n \in Nodes :
        /\ n \notin incoming[n] \cup outgoing[n]
        /\ incoming[n] \cap outgoing[n] = {}

PendingRev(a, b) ==
  \E msg \in mailbox[b] :
     msg.phase = "up" /\ msg.sndr = a /\ msg.reply = "no" /\ ~msg.prune

PendingPrune(a, b) ==
  \E msg \in mailbox[b] : msg.phase = "up" /\ msg.sndr = a /\ msg.prune

NeighborInv ==
  \A n, m \in Nodes :
     /\ m \in incoming[n] => n \in outgoing[m]
     /\ m \in outgoing[n] =>
          \/ n \in incoming[m]
          \/ /\ n \in outgoing[m]
             /\ PendingRev(n, m) \/ PendingRev(m, n)
          \/ /\ n \notin incoming[m] \cup outgoing[m]
             /\ PendingPrune(m, n)

FinishIffTerminated == (~ENABLED Progress) <=> Finished

Liveness == <>Finished

=============================================================================
```