------------------------------ MODULE DijkstraRing ------------------------------

CONSTANTS N, M

(* Assume N ≤ M + 1 *)

VARIABLE counters

pred(i) == (i - 1 + N) MOD N

Action(i) ==
    IF i = 0 THEN
        /\ counters[0] = counters[pred(0)]
        /\ counters' = [counters EXCEPT ![0] = (counters[0]+1) MOD M]
    ELSE
        /\ counters[i] # counters[pred(i)]
        /\ counters' = [counters EXCEPT ![i] = counters[pred(i)]]

Next == \E i \in 0..N-1 : Action(i)

Init == counters \in [0..N-1 -> 0..M-1]

Stable ==
    \E i \in 0..N-1 :
        /\ counters[i] # counters[pred(i)]
        /\ \A j \in 0..N-1 \ {i} : counters[j] = counters[pred(j)]

Stabilization == <> (Stable /\ []Stable)

Spec == Init /\ [][Next]_counters /\ WF_vars(Next)

THEOREM StabilizationIsLiveness == Spec => Stabilization

END MODULE