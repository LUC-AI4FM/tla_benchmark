```tla
[p])
         r  == Reply(st[p], m)
     IN
       /\ st' = [st EXCEPT ![p] = ns]
       /\ tcb' = [tcb EXCEPT ![p] = (ns # "CLOSED")]
       /\ net' = [net EXCEPT ![p] = Tail(@),
                             ![q] = IF r = "NONE" THEN @ ELSE Append(@, r)]
       /\ UNCHANGED passive

-----------------------------------------------------------------------------

Next ==
  \E p \in Peers :
     \/ PassiveOpen(p)
     \/ ActiveOpen(p)
     \/ SendData(p)
     \/ Close(p)
     \/ Abort(p)
     \/ Timeout(p)
     \/ Receive(p)

Fairness ==
  \A p \in Peers :
     /\ WF_vars(Receive(p))
     /\ WF_vars(Timeout(p))
     /\ WF_vars(CloseFromCloseWait(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

TCBConsistent == \A p \in Peers : tcb[p] <=> (st[p] # "CLOSED")

EstablishedSync ==
  (\A p \in Peers : net[p] = <<>>) =>
     \A p \in Peers : st[p] = "ESTABLISHED" => st[Peer(p)] = "ESTABLISHED"

\* Liveness properties

ActiveOpenProgress ==
  \A p \in Peers :
     (st[p] = "SYN-SENT") ~> (st[p] \in {"ESTABLISHED", "CLOSED", "LISTEN"})

TimeWaitTerminates ==
  \A p \in Peers : (st[p] = "TIME-WAIT") ~> (st[p] = "CLOSED" /\ ~tcb[p])

OrderlyCloseTerminates ==
  \A p \in Peers :
     (st[p] \in {"FIN-WAIT-1", "FIN-WAIT-2", "CLOSING", "LAST-ACK"})
        ~> (st[p] = "CLOSED" /\ ~tcb[p])

\* RST semantics: consuming an RST in a synchronized or SYN-SENT state
\* always leads to CLOSED; in SYN-RECEIVED to LISTEN (passive) or CLOSED.
RSTSemantics ==
  [][\A p \in Peers :
       (net[p] # <<>> /\ Head(net[p]) = "RST" /\ Receive(p)
         /\ st[p] \notin {"CLOSED", "LISTEN"})
         => st'[p] \in {"CLOSED", "LISTEN"}]_vars

THEOREM Spec => [](TypeOK /\ TCBConsistent /\ EstablishedSync)
=============================================================================
```