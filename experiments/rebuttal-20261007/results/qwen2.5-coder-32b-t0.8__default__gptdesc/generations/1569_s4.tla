------------------------------- MODULE Bakery -------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS NumProcesses \* Number of processes, assumed to be >= 1

VARIABLES choosing, number, local_max, local_nex, location

Init == /\ choosing = [p \in 1..NumProcesses -> FALSE]
        /\ number   = [p \in 1..NumProcesses -> 0]
        /\ local_max = [p \in 1..NumProcesses -> 0]
        /\ local_nex = [p \in 1..NumProcesses -> 0]
        /\ location = [p \in 1..NumProcesses -> "entry"]

Next == 
    \E p \in 1..NumProcesses : 
        \/ /\ location[p] = "entry"
           /\ choosing' = [choosing EXCEPT ![p] = TRUE]
           /\ local_max' = [local_max EXCEPT ![p] = Max(number)]
           /\ local_nex'[p] = 1
           /\ location' = [location EXCEPT ![p] = "choose"]
        \/ /\ location[p] = "choose"
           /\ \A q \in 1..NumProcesses : 
                (q /= p) /\ choosing[q] -> number' = [number EXCEPT ![q] = local_max[p] + local_nex'[p]]
           /\ \A q \in 1..NumProcesses :
                (q /= p) /\ \neg choosing[q] \/ number[q] < number[p]
                 \/ (number[q] = number[p] /\ q <= p) -> local_nex'[p] = local_nex[p] + 1
           /\ choosing' = [choosing EXCEPT ![p] = FALSE]
           /\ location' = [location EXCEPT ![p] = "request"]
        \/ /\ location[p] = "request"
           /\ \A q \in 1..NumProcesses : 
                (q /= p) -> number[q] < number[p] \/ (number[q] = number[p] /\ q <= p)
           /\ location' = [location EXCEPT ![p] = "critical"]
        \/ /\ location[p] = "critical"
           /\ location' = [location EXCEPT ![p] = "release"]
        \/ /\ location[p] = "release"
           /\ number' = [number EXCEPT ![p] = 0]
           /\ location' = [location EXCEPT ![p] = "entry"]

Spec == /\ Init
        /\ \A p \in 1..NumProcesses : WF_vars(<<Next>>, location, {l \in {"entry", "choose", "request", "critical", "release"} | l > location[p]})
        /\ []\[<<choosing, number, local_max, local_nex, location>> \in Init]
             <<Next>>
           \/<>[]\A p \in 1..NumProcesses : location[p] = "entry" \/ location[p] = "critical"

InvariantMutualExclusion == 
    \A p1, p2 \in 1..NumProcesses : p1 /= p2 /\ location[p1] = "critical" => location[p2] \notin {"choose", "request", "critical"}

InvariantTicketBounds ==
    \A p \in 1..NumProcesses : number[p] <= NumProcesses

Inv == InvariantMutualExclusion /\ InvariantTicketBounds
=============================================================================