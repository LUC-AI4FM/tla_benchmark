------------------------------- MODULE HuangAlgorithm -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Procs, Leader
ASSUME Leader \in Procs /\ Cardinality(Procs) > 1

VARIABLES weights, queues, active

Init == 
    /\ weights = [p \in Procs |-> IF p = Leader THEN 1 ELSE 0]
    /\ queues = [p \in Procs |-> <<>>]
    /\ active = {Leader}

Next ==
    \/ \E p \in (Procs \ {Leader}) \intersect active, q \in Procs \ {p} :
        /\ weights' = [weights EXCEPT ![p] = weights[p] / 2, ![q] = weights[q] + weights[p] / 2]
        /\ queues' = [queues EXCEPT ![q] = Append(queues[q], weights[p] / 2)]
        /\ active' = active \ {p} \cup {q}
    \/ \E p \in (Procs \ {Leader}) \intersect active :
        /\ weights' = [weights EXCEPT ![p] = 0, ![Leader] = weights[Leader] + weights[p]]
        /\ queues' = queues
        /\ active' = active \ {p} \cup {Leader}
    \/ \E p \in (Procs \ {Leader}) :
        /\ queues[p] # <<>>
        /\ LET msg == Head(queues[p])
           q == Tail(queues[p]) IN
        /\ weights' = [weights EXCEPT ![p] = weights[p] + msg]
        /\ queues' = [queues EXCEPT ![p] = q]
        /\ active' = active \cup {p}
    \/ Leader \in active /\ weights[Leader] < 1 :
        /\ weights' = weights
        /\ queues' = queues
        /\ active' = active \ {Leader}
    \/ Leader \notin active /\ \E p \in Procs \ {Leader} :
        /\ queues[p] # <<>>
        /\ LET msg == Head(queues[p])
           q == Tail(queues[p]) IN
        /\ weights' = [weights EXCEPT ![Leader] = weights[Leader] + msg]
        /\ queues' = [queues EXCEPT ![p] = q]
        /\ active' = active

Spec ==
    /\ Init
    /\ [][Next]_<<active, queues>>
    /\ WF_next(<<active, queues>>)

Safe ==
    \/ \A p \in Procs : weights[p] = 0 /\ queues[p] = <<>> /\ Leader \notin active
    \/ \E p \in Procs : weights[p] # 0 \/ queues[p] # <<>> \/ Leader \in active

Live ==
    <>[](\A p \in Procs : weights[p] = 0 /\ queues[p] = <<>> /\ Leader \notin active)

TypeOK ==
    /\ \A p \in Procs : weights[p] \in Nat
    /\ \A p \in Procs : queues[p] \in Seq(Nat)
    /\ \A p \in Procs : Cardinality(queues[p]) < 2^Cardinality(Procs)

StateConstraint ==
    \A p \in Procs : weights[p] = 0 \/ weights[p] = 1 \/ (\E n \in Nat : weights[p] = 1 / (2^n))
    
THEOREM Spec => []Safe
THEOREM Spec => Live

=============================================================================