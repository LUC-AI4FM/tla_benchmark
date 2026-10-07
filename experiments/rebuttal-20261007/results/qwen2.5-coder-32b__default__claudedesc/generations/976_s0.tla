------------------------------- MODULE CircleAlgorithm -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES x, y, pc

Init == 
    /\ x = <<0>> ^ N
    /\ y = <<0>> ^ N
    /\ pc = << "a" >> ^ N

Next ==
    \/ \E i \in 0..N-1 : 
        /\ pc[i] = "a"
        /\ pc' = [pc EXCEPT ![i] = "b"]
        /\ x' = [x EXCEPT ![i] = 1]
        /\ y' = y
    \/ \E i \in 0..N-1 :
        /\ pc[i] = "b"
        /\ pc' = [pc EXCEPT ![i] = "Done"]
        /\ x' = x
        /\ y' = [y EXCEPT ![i] = x[(i-1) % N]]

Spec == Init /\ [][Next]_<<x, y, pc>>

TypeOK ==
    /\ x \in [0..N-1 -> {0, 1}]
    /\ y \in [0..N-1 -> {0, 1}]
    /\ pc \in [0..N-1 -> {"a", "b", "Done"}]

Inv ==
    /\ TypeOK
    /\ \A i \in 0..N-1 : pc[i] = "b" \/ pc[i] = "Done" => x[i] = 1
    /\ (\E i \in 0..N-1 : pc[i] # "Done") \/ (\E i \in 0..N-1 : y[i] = 1)

PCorrect ==
    (\A i \in 0..N-1 : pc[i] = "Done") => (\E i \in 0..N-1 : y[i] = 1)

THEOREM Spec => []Inv
THEOREM Inv /\ [][Next]_<<x, y, pc>> => <>PCorrect

=============================================================================