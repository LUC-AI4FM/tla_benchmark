---------------------------- MODULE RingAlgorithm ----------------------------

EXTENDS Naturals, Sequences, TLC, Integers

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES x, y, pc

(*--algorithm ring
variables x = [i \in 1..N |-> 0], y = [i \in 1..N |-> 0]
process p \in 1..N 
begin
    x[self] := 1;
    y[self] := x[if self = 1 then N else self - 1];
    pc[self] := "done"
end process
end algorithm *)

Init == /\ x \in [1..N -> {0}]
        /\ y \in [1..N -> {0}]
        /\ pc \in [1..N -> {"ready"}]

Next == \/ \E i \in 1..N : pc[i] = "ready" /\ 
                              x' = [x EXCEPT ![i] = 1] /\
                              y' = y /\
                              pc' = [pc EXCEPT ![i] = "updating"]
        \/ \E i \in 1..N : pc[i] = "updating" /\ 
                              y' = [y EXCEPT ![i] = x[IF i = 1 THEN N ELSE i - 1]] /\
                              x' = x /\
                              pc' = [pc EXCEPT ![i] = "done"]

Spec == Init /\ [][Next]_<<pc>>

Safety == \A i \in 1..N : pc[i] = "done" => (\E j \in 1..N : y[j] = 1)

Termination == <>(\A i \in 1..N : pc[i] = "done")

Inv == /\ x \in [1..N -> {0, 1}]
       /\ y \in [1..N -> {0, 1}]
       /\ pc \in [1..N -> {"ready", "updating", "done"}]

TypeOK == \/ Init
          \/ (\E i \in 1..N : pc[i] = "ready" => x \in [1..N -> {0}] /\ y \in [1..N -> {0}])
          \/ (\E i \in 1..N : pc[i] = "updating" => x \in [1..N -> {0, 1}] /\ y \in [1..N -> {0}])
          \/ (\A i \in 1..N : pc[i] = "done" => x \in [1..N -> {0, 1}] /\ y \in [1..N -> {0, 1}])

THEOREM Spec => []TypeOK

THEOREM Spec => []Inv

THEOREM Spec => Safety

THEOREM Spec => Termination

====