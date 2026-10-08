---- MODULE HuangsAlgorithm ----

EXTENDS Naturals, FiniteSets, Reals

CONSTANTS Procs, Leader

VARIABLES active, weight, queue

Init == /\ active = {p \in Procs | TRUE}
        /\ weight = [p \in Procs -> 1.0 / Cardinality(Procs)]
        /\ queue = [p \in Procs -> {}]

SendMsg(p, q) ==
    /\ p \in Procs
    /\ q \in Procs
    /\ p /= q
    /\ weight[p] > 0.0
    /\ \/ \A r \in active: weight[r] = 0.5 * weight[p]
       \/ \E r \in active: weight[r] > 0.5 * weight[p]
    /\ queue' = [queue EXCEPT ![p] = queue[p] \cup {<<q, weight[p] / 2>>}]
    /\ weight' = [weight EXCEPT ![p] = weight[p] - weight[p] / 2]
    /\ UNCHANGED active

RecvMsg(p) ==
    /\ p \in Procs
    /\ /\A q \in queue[p]: q[1] \notin active \/ weight[q[1]] > q[2]
    /\ IF queue[p] = {} THEN
           /\ UNCHANGED weight
       ELSE
           /\ LET msg == CHOOSE m \in queue[p] : TRUE IN
              /\ weight' = [weight EXCEPT ![p] = weight[p] + msg[2]]
              /\ queue' = [queue EXCEPT ![p] = queue[p] \ {msg}]
    /\ UNCHANGED active

Idle(p) ==
    /\ p \in Procs
    /\ (\A q \in queue[p]: q[1] \notin active \/ weight[q[1]] > q[2])
    /\ (weight[p] = 0.5 * (SUM r \in active : weight[r]) => active' = active \ {p})
    /\ UNCHANGED weight
    /\ UNCHANGED queue

Next ==
    \/ \E p, q \in Procs: SendMsg(p, q)
    \/ \E p \in Procs: RecvMsg(p)
    \/ \E p \in Procs: Idle(p)

Spec == Init /\ [][Next]_<<active, weight, queue>>

Safety ==
    /\ (/\A p \in Procs: active[p] => weight[p] > 0.0)
    /\ (\A p \notin active: weight[p] = 0.0)
    /\ (\A p, q \in Procs, m \in queue[p]: m[1] = q)

Termination ==
    /\ (Cardinality(active) = 0)
    /\ (\A p \in Procs: queue[p] = {})

Invariant == \/ Cardinality(active) > 0
             \/ Termination

Liveness == <>(Termination)

Fairness ==
    WF_<<p \in Procs : SendMsg(p, CHOOSE q \in (Procs \ {p}): TRUE)>>_<<active, weight, queue>>
    /\ WF_<<p \in Procs : RecvMsg(p)>>_<<active, weight, queue>>
    /\ SF_<<p \in Procs : Idle(p)>>_<<active, weight, queue>>

CompleteSpec == Spec /\ Invariant /\ Liveness /\ Fairness

====