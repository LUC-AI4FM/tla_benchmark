------------------------------- MODULE SharedMemoryAlgorithm -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N \* Number of processes
ASSUME N > 0

VARIABLES x, y, done

Init == /\ x = <<{0} \: i \in 1..N>>
        /\ y = <<0 \: i \in 1..N>>
        /\ done = {FALSE}

Next == \/ /\ EX /\ i \in 1..N
            /\ ~<<done>>[i]
            /\ x' = [x EXCEPT ![i] = IF Cardinality(x[i]) = 1 THEN x[i] \cup {1} ELSE {1}]
            /\ UNCHANGED <<y, done>>
        \/ /\ ER /\ i \in 1..N
            /\ ~<<done>>[i]
            /\ x'[i] = x[i]
            /\ y' = [y EXCEPT ![i] = CHOOSE v \in (x[<<i % N + 1>>)]: TRUE]
            /\ done' = {TRUE}
            /\ UNCHANGED <<x>>
        \/ /\ ET /\ i \in 1..N
            /\ ~<<done>>[i]
            /\ x'[i] = x[i]
            /\ y'[i] = CHOOSE v \in (x[<<i % N + 1>>)]: TRUE]
            /\ done' = {TRUE}
            /\ UNCHANGED <<x>>

Spec == Init /\ [][Next]_<<x, y, done>> /\ <>Termination

Termination == <>(\A i \in 1..N: <<done>>[i])

PCorrect == Spec => []<>(\E i \in 1..N: y[i] = 1)

Inv == [](Cardinality(x[i]) \leq 2 \/ \A i \in 1..N) /\ [](\A i \in 1..N: <<done>>[i] => Cardinality(x[i]) = 1)

================================================================================