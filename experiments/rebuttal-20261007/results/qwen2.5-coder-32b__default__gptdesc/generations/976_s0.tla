------------------------------- MODULE RingAlgorithm -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES x, y, pc

Init == 
    /\ x = <<0>> ^ N
    /\ y = <<0>> ^ N
    /\ pc = [i \in 1..N |-> "start"]

Next ==
    \/ \E i \in 1..N : 
        /\ pc[i] = "start"
        /\ x' = [x EXCEPT ![i] = 1]
        /\ y' = y
        /\ pc' = [pc EXCEPT ![i] = "copy"]
    \/ \E i \in 1..N :
        /\ pc[i] = "copy"
        /\ LET left = IF i = 1 THEN N ELSE i - 1
        IN x' = x
           /\ y' = [y EXCEPT ![i] = x[left]]
           /\ pc' = [pc EXCEPT ![i] = "done"]

Spec ==
    /\ Init
    /\ [][Next]_<<x, y, pc>>
    /\ <><\A i \in 1..N : pc[i] = "done">>_<<x, y, pc>>

Inv ==
    \/ \E i \in 1..N : pc[i] = "start"
    \/ \E i \in 1..N : pc[i] = "copy" /\ (\A j \in 1..i-1 : pc[j] = "done")
    \/ \A i \in 1..N : pc[i] = "done"

Safety ==
    <><\E i \in 1..N : y[i] = 1>>_<<x, y, pc>>

TypeOK ==
    /\ x \in [1..N -> {0, 1}]
    /\ y \in [1..N -> {0, 1}]
    /\ pc \in [1..N -> {"start", "copy", "done"}]

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => Safety

=============================================================================