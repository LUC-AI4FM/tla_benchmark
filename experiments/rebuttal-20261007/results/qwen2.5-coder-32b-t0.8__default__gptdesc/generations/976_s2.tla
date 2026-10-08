------------------------------- MODULE RingAlgorithm -------------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES x, y, pc

Proc == 1..N

Init == 
    /\ x = <<0>>^N
    /\ y = <<0>>^N
    /\ pc = [p \in Proc |-> "start"]

Next ==
    \/ /\ pc[1] = "start"
       /\ x' = [x EXCEPT ![1] = 1]
       /\ pc' = [pc EXCEPT ![1] = "copy"]
    \/ \/ /\ /\ p \in 2..N
              /\ pc[p] = "start"
              /\ x' = [x EXCEPT ![p] = 1]
              /\ pc' = [pc EXCEPT ![p] = "copy"]
       \/ /\ /\ p \in Proc
              /\ pc[p] = "copy"
              /\ y' = [y EXCEPT ![p] = x[p-1]]
              /\ pc' = [pc EXCEPT ![p] = "done"]
    \/ /\ pc[1] = "copy"
       /\ y' = [y EXCEPT ![1] = x[N]]
       /\ pc' = [pc EXCEPT ![1] = "done"]

Inv ==
    \A p \in Proc: (pc[p] = "start" => x[p] = 0)
    /\ \A p \in Proc: (pc[p] = "copy" => x[p] = 1)
    /\ \A p \in Proc: (pc[p] = "done" => y[p] = \/ q \in {p-1} \cup {N |-> p=1}: x[q])

Spec ==
    /\ Init
    /\ [][Next]_<<x, y, pc>>
    /\ WF_next(<<x, y, pc>>)

Termination ==
    <>[](\A p \in Proc: pc[p] = "done")

Safety ==
    <>(\E p \in Proc: y[p] = 1)

THEOREM Spec => []Inv
THEOREM Spec => Termination /\ Safety

=============================================================================