------------------------------- MODULE HuangTermination ----------------------------------
EXTENDS Naturals, Reals, FiniteSets

CONSTANTS Procs, Leader
ASSUME Procs \subseteq Nat /\ Cardinality(Procs) > 1 /\ Leader \in Procs

VARIABLES active, weight, queue

Init == 
    /\ active = {p \in Procs | TRUE}
    /\ weight = [p \in Procs -> 1.0 / Cardinality(Procs)]
    /\ queue = [p \in Procs -> <>]

SendMsg(p, q) ==
    /\ p \in Procs
    /\ q \in (Procs \ {p})
    /\ active[p]
    /\ LET halfWeight == weight[p] / 2.0
       IN /\ weight' = [weight EXCEPT ![p] = weight[p] - halfWeight, ![q] = weight[q] + halfWeight]
          /\ queue' = [queue EXCEPT ![q] = Append(queue[q], <<p, halfWeight>>)]
          /\ active' = active

ReceiveMsg(p) ==
    /\ p \in Procs
    /\ Len(queue[p]) > 0
    /\ LET msg == Head(queue[p])
       IN /\ weight' = [weight EXCEPT ![msg[1]] = weight[msg[1]] - msg[2], ![p] = weight[p] + msg[2]]
          /\ queue' = [queue EXCEPT ![p] = Tail(queue[p])]
          /\ active' = IF Sum({w \in DOMAIN weight | w \notin {msg[1], p}}: weight[w]) = 0 
                        THEN active \ {msg[1]} ELSE active

Idle(p) ==
    /\ p \in Procs
    /\ queue[p] = <>
    /\ (\E q \in (Procs \ {p}): queue[q] = <>)
    /\ weight[p] > 0.0
    /\ weight' = weight
    /\ queue' = queue
    /\ active' = active

Next ==
    \/ (\E p, q \in Procs: SendMsg(p, q))
    \/ (\E p \in Procs: ReceiveMsg(p))
    \/ (\E p \in Procs: Idle(p))

Spec == 
    /\ Init
    /\ [][Next]_<<active, weight, queue>>
    /\ SF_\forall p \in Procs : (SendMsg(p, _) \/ ReceiveMsg(p) \/ Idle(p)) <<active, weight, queue>>

\* Safety properties
TerminationDetected ==
    /\ active = {}
    /\ (\A p \in Procs: queue[p] = <>)

Safety == 
    G(Init => TerminationDetected => (\A p \in Procs: weight[p] = 0.0))
    
\* Liveness property
TerminationEventual ==
    <>(active = {})

Liveness ==
    [](Init => TerminationEventual)
    
=============================================================================