```tla
 = "source"
    /\ phase[n] = "down"
    /\ mailbox' = [m \in Nodes |->
                     IF m \in outgoing[n] THEN mailbox[m] \cup {DownMsg(n, n)}
                     ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<incoming, outgoing, active>>

DownInternal(n) ==
    /\ kind(n) = "internal"
    /\ phase[n] = "down"
    /\ ReceivedAllDown(n)
    /\ LET mn == Min({msg.val : msg \in DownFrom(n)})
       IN  mailbox' = [m \in Nodes |->
                         IF m \in outgoing[n] THEN mailbox[m] \cup {DownMsg(n, mn)}
                         ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<incoming, outgoing, active>>

DownSink(n) ==
    /\ kind(n) = "sink"
    /\ phase[n] = "down"
    /\ ReceivedAllDown(n)
    /\ LET dm   == DownFrom(n)
           vals == {msg.val : msg \in dm}
           mn   == Min(vals)
           minS == {msg.sndr : msg \in {x \in dm : x.val = mn}}
           keep == Min(minS)
           leaf == vals = {mn}
           rep(m) == IF m \in minS THEN "yes" ELSE "no"
           prn(m) == IF leaf THEN TRUE ELSE (m \in minS /\ m # keep)
       IN  /\ mailbox' = [m \in Nodes |->
                            IF m = n THEN mailbox[n] \ dm
                            ELSE IF m \in incoming[n]
                                 THEN mailbox[m] \cup {UpMsg(n, rep(m), prn(m))}
                                 ELSE mailbox[m]]
           /\ IF leaf
              THEN /\ incoming' = [incoming EXCEPT ![n] = {}]
                   /\ active' = [active EXCEPT ![n] = FALSE]
                   /\ UNCHANGED outgoing
              ELSE /\ incoming' = [incoming EXCEPT ![n] = {keep}]
                   /\ outgoing' = [outgoing EXCEPT ![n] = incoming[n] \ minS]
                   /\ UNCHANGED active
    /\ UNCHANGED phase

UpSource(n) ==
    /\ kind(n) = "source"
    /\ phase[n] = "up"
    /\ ReceivedAllUp(n)
    /\ LET um   == UpFrom(n)
           rev  == {msg.sndr : msg \in {x \in um : x.reply = "no" /\ ~x.prune}}
           gone == {msg.sndr : msg \in {x \in um : x.reply = "no" \/ x.prune}}
       IN  /\ outgoing' = [outgoing EXCEPT ![n] = @ \ gone]
           /\ incoming' = [incoming EXCEPT ![n] = @ \cup rev]
           /\ mailbox' = [mailbox EXCEPT ![n] = @ \ um]
    /\ phase' = [phase EXCEPT ![n] = "down"]
    /\ UNCHANGED active

UpInternal(n) ==
    /\ kind(n) = "internal"
    /\ phase[n] = "up"
    /\ ReceivedAllUp(n)
    /\ LET um   == UpFrom(n)
           dm   == DownFrom(n)
           vals == {msg.val : msg \in dm}
           mn   == Min(vals)
           minS == {msg.sndr : msg \in {x \in dm : x.val = mn}}
           keep == Min(minS)
           anyNo == \E msg \in um : msg.reply = "no"
           rep(m) == IF ~anyNo /\ m \in minS THEN "yes" ELSE "no"
           prn(m) == m \in minS /\ m # keep
           revOut  == {msg.sndr : msg \in {x \in um : x.reply = "no" /\ ~x.prune}}
           goneOut == {msg.sndr : msg \in {x \in um : x.reply = "no" \/ x.prune}}
           revIn   == {m \in incoming[n] : rep(m) = "no" /\ ~prn(m)}
           goneIn  == {m \in incoming[n] : rep(m) = "no" \/ prn(m)}
       IN  /\ outgoing' = [outgoing EXCEPT ![n] = (@ \ goneOut) \cup revIn]
           /\ incoming' = [incoming EXCEPT ![n] = (@ \ goneIn) \cup revOut]
           /\ mailbox' = [m \in Nodes |->
                            IF m = n THEN mailbox[n] \ (um \cup dm)
                            ELSE IF m \in incoming[n]
                                 THEN mailbox[m] \cup {UpMsg(n, rep(m), prn(m))}
                                 ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "down"]
    /\ UNCHANGED active

Node(n) ==
    \/ DownSource(n)
    \/ DownInternal(n)
    \/ DownSink(n)
    \/ UpSource(n)
    \/ UpInternal(n)

Terminated ==
    /\ \A n \in Nodes : IF n = 1 THEN kind(n) = "leader" ELSE ~active[n]
    /\ \A n \in Nodes : mailbox[n] = {}

Next ==
    \/ \E n \in Nodes : Node(n)
    \/ Terminated /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ \A n \in Nodes : WF_vars(Node(n))

-----------------------------------------------------------------------------

TypeOK ==
    /\ phase \in [Nodes -> {"down", "up"}]
    /\ incoming \in [Nodes -> SUBSET Nodes]
    /\ outgoing \in [Nodes -> SUBSET Nodes]
    /\ mailbox \in [Nodes -> SUBSET Messages]
    /\ active \in [Nodes -> BOOLEAN]

Pending(a, b) ==
    \E msg \in mailbox[a] :
        /\ msg.phase = "up"
        /\ msg.sndr = b
        /\ (msg.reply = "no" \/ msg.prune)

NeighborInv ==
    \A m, n \in Nodes :
        \/ (n \in outgoing[m] <=> m \in incoming[n])
        \/ Pending(m, n)
        \/ Pending(n, m)

FinishIffTerminated ==
    (~ ENABLED (\E n \in Nodes : Node(n))) <=> Terminated

Liveness == <>[]Terminated

=============================================================================
```