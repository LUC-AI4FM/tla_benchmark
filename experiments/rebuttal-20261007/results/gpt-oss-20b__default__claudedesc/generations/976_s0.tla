MODULE SimpleConcurrent
EXTENDS Naturals

CONSTANT N

VARIABLES x, y, pc

(* Helper to compute left neighbor index *)
Left(i) == ((i - 1 + N) % N)

TypeOK ==
    /\ x \in [0..N-1 -> {0,1}]
    /\ y \in [0..N-1 -> {0,1}]
    /\ pc \in [0..N-1 -> {"a","b","Done"}]

Init ==
    /\ x = [i \in 0..N-1 |-> 0]
    /\ y = [i \in 0..N-1 |-> 0]
    /\ pc = [i \in 0..N-1 |-> "a"]

Next ==
    \E i \in 0..N-1 :
        (pc[i] = "a" /\
         x' = [x EXCEPT ![i] = 1] /\
         y' = y /\
         pc' = [pc EXCEPT ![i] = "b"])
     \/ (pc[i] = "b" /\
         y' = [y EXCEPT ![i] = x[Left(i)]] /\
         pc' = [pc EXCEPT ![i] = "Done"] /\ 
         x' = x)

Inv ==
    TypeOK
    /\ \A i \in 0..N-1 : (pc[i] = "b" \/ pc[i]="Done") => x[i] = 1
    /\ (\E i \in 0..N-1 : pc[i] /= "Done") \/ (\E i \in 0..N-1 : y[i] = 1)

PCorrect ==
    (\A i \in 0..N-1 : pc[i] = "Done") => (\E i \in 0..N-1 : y[i] = 1)

Spec == Init /\ [][Next]_<<x, y, pc>>

THEOREM Correctness: Spec => []Inv
THEOREM Correctness2: Spec => []PCorrect

===============================================================================