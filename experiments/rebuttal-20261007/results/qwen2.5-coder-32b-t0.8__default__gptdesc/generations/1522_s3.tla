---- MODULE HuangTerminationDetection ----

EXTENDS Naturals, Reals, Sequences, FiniteSets

CONSTANTS Procs, Leader

VARIABLES active, weight, queue

Init == /\ active = {p \in Procs : TRUE}
        /\ weight = [p \in Procs -> 1.0 / Cardinality(Procs)]
        /\ queue = [p \in Procs -> <<>>]

SendMsg(p, q, w) ==
    /\ p \in active
    /\ w <= weight[p]
    /\ weight' = [weight EXCEPT ![p] = weight[p] - w, ![q] = weight[q] + w]
    /\ queue' = [queue EXCEPT ![q] = Append(queue[q], <<p, w>>)]

ReceiveMsg(p) ==
    /\ p \in active
    /\ queue[p] /= <<>>
    /\ LET msg == Head(queue[p]) IN
       /\ /\ weight' = [weight EXCEPT ![msg[1]] = weight[msg[1]] - msg[2]]
          /\ queue' = [queue EXCEPT ![p] = Tail(queue[p])]
          /\ queue'[msg[1]] = Append(queue[msg[1]], <<p, msg[2]/2>>)
          /\ queue'[p] = Append(queue'[p], <<msg[1], msg[2]/2>>)

Idle(p) ==
    /\ p \in active
    /\ weight[p] = 0.0
    /\ queue[p] = <<>>
    /\ IF p = Leader THEN /\ active' = {}
                           /\ queue' = [q \in Procs -> <<>>]
                         ELSE /\ weight' = weight
                            /\ queue' = queue

Next ==
    \/ \E p, q \in Procs, w \in 0..1.0 : SendMsg(p, q, w)
    \/ \E p \in Procs : ReceiveMsg(p)
    \/ \E p \in Procs : Idle(p)

Spec ==
    /\ Init
    /\ [][Next]_<<active, weight, queue>>
    /\ WF_<<p \in active >> SendMsg(p, CHOOSE q \in Procs \ {p} : TRUE, CHOOSE w \in 0..1.0 : TRUE)
    /\ SF_\E p \in Procs : Idle(p)

Invariant ==
    \/ /\ \A p \notin active : weight[p] = 0.0
       /\ \A p \notin active : queue[p] = <<>>
       /\ \A q \in Procs, m \in queue[q] : m[1] \notin active
       /\ \A p \in active : weight[p] > 0.0
    \/ /\ \A p \in Procs : weight[p] = 0.0
       /\ \A p \in Procs : queue[p] = <<>>
       /\ active = {}

Termination ==
    \E s \in StateSuchThat(Invariant) : \A p \in Procs : p \notin active[s]

Spec == Spec /\ []Invariant /\ <>(Termination)

====