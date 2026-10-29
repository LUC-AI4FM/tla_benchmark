 : msg \in upMsgs} = outgoing[n]
         /\ active' = [active EXCEPT ![n] = ~isLone]
         /\ incoming' = [incoming EXCEPT ![n] =
               IF isLone THEN {}
               ELSE {k \in incoming[n] : reply(k) = "yes" /\ ~prune(k)}
                    \cup (noSndrs \ prSndrs)]
         /\ outgoing' = [outgoing EXCEPT ![n] =
               IF isLone THEN {}
               ELSE (outgoing[n] \ (noSndrs \cup prSndrs))
                    \cup {k \in incoming[n] : reply(k) = "no"}]
         /\ mailbox' = [k \in Nodes |->
               IF k = n
               THEN {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \notin incoming[n]}
               ELSE IF k \in incoming[n]
                    THEN mailbox[k] \cup {upMsg(n, reply(k), prune(k))}
                    ELSE mailbox[k]]
  /\ phase' = [phase EXCEPT ![n] = "down"]

-----------------------------------------------------------------------------

Next == \E n \in Nodes :
          \/ DownSource(n)
          \/ DownOther(n)
          \/ UpSource(n)
          \/ UpOther(n)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A n \in Nodes :
       /\ WF_vars(DownSource(n))
       /\ WF_vars(DownOther(n))
       /\ WF_vars(UpSource(n))
       /\ WF_vars(UpOther(n))

-----------------------------------------------------------------------------
(* Properties *)

NeighborInv ==
  \A n, m \in Nodes :
    /\ m \in incoming[n] => n \in outgoing[m]
    /\ m \in outgoing[n] =>
         \/ n \in incoming[m]
         \/ \E msg \in mailbox[n] :
               /\ msg.phase = "up"
               /\ msg.sndr = m
               /\ (msg.reply = "no" \/ msg.prune)
         \/ \E msg \in mailbox[m] :
               /\ msg.phase = "up"
               /\ msg.sndr = n
               /\ msg.reply = "no"
               /\ ~msg.prune

NoNewSource ==
  [][\A n \in Nodes :
       (active'[n] /\ incoming'[n] = {}) => incoming[n] = {}]_vars

Terminated ==
  LET l == Min(Nodes)
  IN  /\ active[l]
      /\ incoming[l] = {}
      /\ outgoing[l] = {}
      /\ \A n \in Nodes \ {l} : ~active[n]
      /\ \A n \in Nodes : mailbox[n] = {}

FinishIffTerminated == (~ENABLED Next) <=> Terminated

Liveness == <>Terminated

=============================================================================
```