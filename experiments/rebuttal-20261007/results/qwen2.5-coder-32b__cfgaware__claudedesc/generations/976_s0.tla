------------------------------- MODULE CircleAlgorithm -------------------------------

CONSTANTS N \* Assumed to be a positive natural number; fixed to 5 in model-checking config

VARIABLES x, y, pc \* Shared arrays and program-counter array

\* Initialization predicate
Init == /\ x = [i \in 0..N-1 -> 0]
        /\ y = [i \in 0..N-1 -> 0]
        /\ pc = [i \in 0..N-1 -> "a"]

\* Type-correctness invariant
TypeOK ==
    /\ x \in [0..N-1 -> {0, 1}]
    /\ y \in [0..N-1 -> {0, 1}]
    /\ pc \in [0..N-1 -> {"a", "b", "Done"}]

\* Additional invariants
Inv ==
    /\ TypeOK
    /\ \A i \in 0..N-1 : pc[i] \notin {"a", "b"} \/ x[i] = 1
    /\ (\E i \in 0..N-1 : pc[i] \in {"a", "b"}) \/ (\E i \in 0..N-1 : y[i] = 1)

\* Core correctness property
PCorrect ==
    /\ \A i \in 0..N-1 : pc[i] = "Done"
    /\ \E i \in 0..N-1 : y[i] = 1

\* Next-state relation
Next ==
    \E i \in 0..N-1 :
        \/ /\ pc[i] = "a"
           /\ x' = [x EXCEPT ![i] = 1]
           /\ y' = y
           /\ pc' = [pc EXCEPT ![i] = "b"]
        \/ /\ pc[i] = "b"
           /\ LET leftNeighbor == (i - 1) % N IN
              x' = x
              /\ y' = [y EXCEPT ![i] = x[leftNeighbor]]
              /\ pc' = [pc EXCEPT ![i] = "Done"]

\* Specification
Spec ==
    Init /\ [][Next]_<<x, y, pc>>

THEOREM Spec => []PCorrect

=============================================================================