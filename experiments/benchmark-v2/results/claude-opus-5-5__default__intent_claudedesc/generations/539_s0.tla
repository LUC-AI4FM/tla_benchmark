------------------------------ MODULE Squares ------------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat

VARIABLES n, a, i, pc

vars == <<n, a, i, pc>>

Init ==
    /\ n  = N
    /\ a  = [j \in 0..N |-> 0]
    /\ i  = 0
    /\ pc = "Loop"

Step ==
    /\ pc = "Loop"
    /\ a' = [a EXCEPT ![i] = i * i]
    /\ IF i = n
          THEN /\ pc' = "Done"
               /\ i'  = i
          ELSE /\ i'  = i + 1
               /\ pc' = "Loop"
    /\ UNCHANGED n

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Step \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ n \in Nat
    /\ a \in [0..n -> 0..(n * n)]
    /\ i \in 0..n
    /\ pc \in {"Loop", "Done"}

LoopInvariant ==
    /\ pc = "Loop" => \A j \in 0..(i - 1) : a[j] = j * j
    /\ pc = "Done" => \A j \in 0..n : a[j] = j * j

Correctness ==
    pc = "Done" => \A j \in 0..n : a[j] = j * j

-----------------------------------------------------------------------------
(* Liveness property *)

Termination == <>(pc = "Done")

FinalCorrectness == <>(\A j \in 0..n : a[j] = j * j)

=============================================================================