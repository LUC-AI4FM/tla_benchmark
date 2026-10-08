------------------------------- MODULE HuangTermination -------------------------------
EXTENDS Naturals, Reals, FiniteSets

CONSTANTS Procs, Leader

VARIABLES active, weight, queue

Init == /\ active = {p \in Procs: TRUE}
        /\ weight = [p \in Procs -> 1.0 / Cardinality(Procs)]
        /\ queue = [p \in Procs -> {}]

SendMsg(p, q) ==
    /\ p \in Procs
    /\ q \in Procs
    /\ p /= q
    /\ active[p]
    /\ weight[p] > 0.0
    /\ queue' = [queue EXCEPT ![p] = Append(queue[p], <<q, weight[p] / 2>>)]
    /\ weight' = [weight EXCEPT ![p] = weight[p] - weight[p] / 2]
    /\ UNCHANGED <<active, queue[q]>>

RecvMsg(p) ==
    /\ p \in Procs
    /\ active[p]
    /\ queue[p] /= {}
    /\ LET msg == Head(queue[p])
       IN /\ queue' = [queue EXCEPT ![p] = Tail(queue[p])]
          /\ weight' = [weight EXCEPT ![msg[1]] = weight[msg[1]] + msg[2]]
          /\ UNCHANGED <<active, queue[EXCEPT ![p] -> _]>>

Idle(p) ==
    /\ p \in Procs
    /\ active[p]
    /\ queue[p] = {}
    /\ weight[p] > 0.0
    /\ weight' = weight
    /\ queue' = queue

Next ==
    \/ \E p, q \in Procs : SendMsg(p, q)
    \/ \E p \in Procs : RecvMsg(p)
    \/ \E p \in Procs : Idle(p)

Spec ==
    /\ Init
    /\ [][Next]_<<active, weight, queue>>
    /\ WF_next(<<active, weight, queue>>)

TerminationDetected ==
    /\ \A p \in Procs : ~active[p]
    /\ \A p \in Procs : queue[p] = {}

Safety == Spec => [](\A p \in Procs : 0.0 <= weight[p] <= 1.0)
          /\ Spec => [](Sum({weight[p] + Sum(queue[p]) : p \in Procs}) = 1.0)

Liveness ==
    Spec => <>(TerminationDetected)

THEOREM Spec => []Safety
THEOREM Spec => <>Liveness

=============================================================================