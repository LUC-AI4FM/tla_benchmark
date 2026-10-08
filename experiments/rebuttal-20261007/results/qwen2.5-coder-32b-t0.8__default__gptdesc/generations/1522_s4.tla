```tla
------------------------------ MODULE HuangTermination ------------------------------

EXTENDS Naturals, Reals, FiniteSets

CONSTANTS Procs, Leader

VARIABLES active, weight, queue

(* --algorithm HuangTermination *)

Init == /\ active = {p \in Procs: TRUE}
        /\ weight = [p \in Procs |-> 1.0 / Cardinality(Procs)]
        /\ queue = [p \in Procs |-> {}]

Send(m, sender, receiver) ==
    /\ active[receiver]
    /\ m \notin queue[sender]
    /\ /\ queue' = [queue EXCEPT ![sender] = queue[sender] \cup {m}]
       /\ weight' = weight
       /\ active' = active

Receive(m, receiver) ==
    /\ m \in queue[receiver]
    /\ /\ queue' = [queue EXCEPT ![receiver] = queue[receiver] \ {m}]
       /\ weight' = [weight EXCEPT ![receiver] = weight[receiver] + m.weight / 2.0]
       /\ active'[receiver] = IF weight'[receiver] >= 1.0 THEN {} ELSE {receiver}

Idle(p) ==
    /\ p /= Leader
    /\ queue[p] = {}
    /\ weight[p] < 1.0
    /\ /\ queue' = queue
       /\ weight' = [weight EXCEPT ![p] = weight[p] / 2.0]
       /\ active'[p] = IF weight'[p] >= 1.0 THEN {} ELSE {p}

Next ==
    \/ \E m \in SUBSET Procs, sender \in Procs, receiver \in (Procs \ {sender}) :
        Send(m, sender, receiver)
    \/ \E m \in Procs, receiver \in Procs :
        Receive(m, receiver)
    \/ \E p \in Procs :
        Idle(p)

Spec ==
    /\ Init
    /\ [][Next]_<<active>>
    /\ WF_next(<<active>>)

TermDetected ==
    /\ queue = [p \in Procs |-> {}]
    /\ weight = [p \in Procs |-> 1.0]
    /\ active = {}

Inv1 == \A p \in Procs : weight[p] >= 0.0

Inv2 == Sum(p \in Procs : weight[p]) + Sum(p \in Procs, m \in queue[p] : m.weight) = 1.0

Inv3 == Leader \notin active \/ (queue[Leader] = {})

Spec ==
    /\ Init
    /\ [][Next]_<<active>>
    /\ WF_next(<<active>>)
    /\ Spec => [](Inv1 /\ Inv2 /\ Inv3)
    /\ <>(TermDetected)

(* --end-module-- *)
```