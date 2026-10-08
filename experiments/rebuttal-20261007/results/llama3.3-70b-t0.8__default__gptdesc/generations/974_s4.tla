```tla
MODULE SharedMemoryAlgorithm

EXTENDS Integers, Sequences

CONSTANTS N
VARIABLES x, y, done, pc

Init == (* Initial condition *)
        /\ x = [i \in 1..N |-> {0}]
        /\ y = [i \in 1..N |-> 0]
        /\ done = [i \in 1..N |-> FALSE]
        /\ pc = [i \in 1..N |-> "start"]

Next == (* Next-state relation *)
        \/ \E i \in 1..N :
            pc[i] = "start"
            /\ x' = [x EXCEPT ![i] = {0, 1}]
            /\ y' = y
            /\ done' = done
            /\ pc' = [pc EXCEPT ![i] = "write1"]
        \/ \E i \in 1..N :
            pc[i] = "write1"
            /\ x' = [x EXCEPT ![i] = {1}]
            /\ y' = y
            /\ done' = done
            /\ pc' = [pc EXCEPT ![i] = "read"]
        \/ \E i \in 1..N :
            pc[i] = "read"
            /\ \E v \in x[(i % N) + 1] : 
                y' = [y EXCEPT ![i] = v]
            /\ x' = x
            /\ done' = [done EXCEPT ![i] = TRUE]
            /\ pc' = [pc EXCEPT ![i] = "done"]

Spec == (* Specification *)
        Init /\ [][Next]_<<x, y, done, pc>>

PCorrect == (* Safety property: if all processes are done, then some y[i] equals 1 *)
        \A i \in 1..N : done[i]
        => \E i \in 1..N : y[i] = 1

Inv == (* Inductive invariant *)
        /\ \A i \in 1..N : pc[i] \in {"start", "write1", "read", "done"}
        /\ \A i \in 1..N : done[i] => pc[i] = "done"
        /\ \A i \in 1..N : x[i] \subseteq {0, 1}

THEOREM Spec => []PCorrect
PROOF OMITTED

THEOREM Spec => <<x, y, done, pc>>_inv
PROOF OMITTED

Fairness == (* Fairness condition *)
        \A i \in 1..N : <>pc[i] = "done"

THEOREM Spec /\ Fairness => []PCorrect
PROOF OMITTED
```