--------------------------- MODULE DiningPhilosophers ---------------------------
EXTENDS Naturals, Sequences

CONSTANT N

VARIABLES sem, pc

(* -- definitions of fork positions and philosopher states -- *)
LEFT(i) == i
RIGHT(i) == (i + 1) % N

States == {"hungry", "acquireR", "acquireL", "eating"}

Init ==
    /\ N > 0
    /\ sem = [i \in 0..N-1 |-> TRUE]
    /\ pc   = [i \in 0..N-1 |-> "hungry"]

(* -- actions for philosophers 1 .. N-1 (right then left) -- *)
AcquireRight(i) ==
    /\ i \in 1..N-1
    /\ pc[i] = "hungry"
    /\ sem[RIGHT(i)] = TRUE
    /\ sem' = [sem EXCEPT ![RIGHT(i)] = FALSE]
    /\ pc'   = [pc EXCEPT ![i] = "acquireL"]

AcquireLeft(i) ==
    /\ i \in 1..N-1
    /\ pc[i] = "acquireL"
    /\ sem[LEFT(i)] = TRUE
    /\ sem' = [sem EXCEPT ![LEFT(i)] = FALSE]
    /\ pc'   = [pc EXCEPT ![i] = "eating"]

ReleaseForks(i) ==
    /\ i \in 1..N-1
    /\ pc[i] = "eating"
    /\ sem' = [sem EXCEPT ![RIGHT(i)] = TRUE, ![LEFT(i)] = TRUE]
    /\ pc'   = [pc EXCEPT ![i] = "hungry"]

(* -- actions for philosopher 0 (left then right) -- *)
AcquireLeft0 ==
    /\ pc[0] = "hungry"
    /\ sem[LEFT(0)] = TRUE
    /\ sem' = [sem EXCEPT ![LEFT(0)] = FALSE]
    /\ pc'   = [pc EXCEPT ![0] = "acquireR"]

AcquireRight0 ==
    /\ pc[0] = "acquireR"
    /\ sem[RIGHT(0)] = TRUE
    /\ sem' = [sem EXCEPT ![RIGHT(0)] = FALSE]
    /\ pc'   = [pc EXCEPT ![0] = "eating"]

ReleaseForks0 ==
    /\ pc[0] = "eating"
    /\ sem' = [sem EXCEPT ![LEFT(0)] = TRUE, ![RIGHT(0)] = TRUE]
    /\ pc'   = [pc EXCEPT ![0] = "hungry"]

Next == \/ \E i \in 1..N-1 : AcquireRight(i)
        \/ \E i \in 1..N-1 : AcquireLeft(i)
        \/ \E i \in 1..N-1 : ReleaseForks(i)
        \/ AcquireLeft0
        \/ AcquireRight0
        \/ ReleaseForks0

(* fairness condition: strong fairness for the next action *)
Fairness == WF_liveness[Next]_vars

Spec == Init /\ [][Next]_vars /\ Fairness

(* adjacency predicate *)
Adjacent(i, j) ==
    j = RIGHT(i) \/ i = RIGHT(j)

MutualExcl ==
    ∀ i, j \in 0..N-1 : Adjacent(i,j)
        => ~(pc[i] = "eating" /\ pc[j] = "eating")

Theorem MutualExclusionThm == Spec => [] MutualExcl

StarvationFreedom ==
    ∀ i \in 0..N-1 : [](<>(pc[i] = "eating"))

Theorem StarvationThm == Spec => StarvationFreedom
=============================================================================