---------------------------- MODULE SharedMemory ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE x, y, done

Spec == /\ x = [i \in 1..N |-> {0}]
        /\ y = [i \in 1..N |-> 0]
        /\ done = [i \in 1..N |-> FALSE]

TypeOK == /\ x \in [1..N -> SUBSET Int]
          /\ y \in [1..N -> Int]
          /\ done \in [1..N -> BOOLEAN]

Write(i, v) == /\ x' = [x EXCEPT ![i] = x[i] \cup {v}]
               /\ y' = y
               /\ done' = done

Read(i, j) == /\ x' = x
               /\ y' = [y EXCEPT ![i] = CHOOSE v \in x[j]]
               /\ done' = [done EXCEPT ![i] = TRUE]

Next == \/ \E i \in 1..N : Write(i, 1)
          \/ \E i \in 1..N : Read(i, (i mod N) + 1)

PCorrect == <>[]<>(\A i \in 1..N : done[i]) => <>(\E i \in 1..N : y[i] = 1)

Inv == /\ TypeOK
        /\ \A i \in 1..N : (done[i] => \E j \in 1..N : y[j] = 1)
        /\ \A i \in 1..N : x[i] /= {} 

THEOREM Spec => []PCorrect
PROOF BY induction, INVARIANT Inv

THEOREM Spec => <>[]Inv
PROOF BY induction

=============================================================================