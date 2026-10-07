------------------------------- MODULE DiningPhilosophers -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N
ASSUME N \in Nat /\ N >= 2

VARIABLES sem, pc

Init == 
    /\ sem = <<1, 1, 1, 1>>
    /\ pc = [i \in 0..N-1 |-> IF i = 0 THEN "l01" ELSE "l1"]

Next ==
    \/ /\ pc[0] = "l01"
       /\ sem[0] = 1
       /\ sem[N-1] = 1
       /\ LET newSem == [sem EXCEPT ![0] = 0, ![N-1] = 0]
          newPc == [pc EXCEPT ![0] = "l02"]
       IN \/ /\ sem' = newSem
          /\ pc' = newPc
    \/ /\ pc[0] = "l02"
       /\ LET newPc == [pc EXCEPT ![0] = "l03"]
       IN \/ /\ sem' = sem
          /\ pc' = newPc
    \/ /\ pc[0] = "l03"
       /\ LET newSem == [sem EXCEPT ![0] = 1, ![N-1] = 1]
          newPc == [pc EXCEPT ![0] = "l04"]
       IN \/ /\ sem' = newSem
          /\ pc' = newPc
    \/ /\ pc[0] = "l04"
       /\ LET newPc == [pc EXCEPT ![0] = "l01"]
       IN \/ /\ sem' = sem
          /\ pc' = newPc
    \/ \E i \in 1..N-1 :
        \/ /\ pc[i] = "l1"
           /\ sem[i] = 1
           /\ LET newSem == [sem EXCEPT ![i] = 0]
              newPc == [pc EXCEPT ![i] = "l2"]
           IN \/ /\ sem' = newSem
              /\ pc' = newPc
        \/ /\ pc[i] = "l2"
           /\ sem[(i+1) % N] = 1
           /\ LET newSem == [sem EXCEPT ![i] = 0, ![(i+1) % N] = 0]
              newPc == [pc EXCEPT ![i] = "l3"]
           IN \/ /\ sem' = newSem
              /\ pc' = newPc
        \/ /\ pc[i] = "l3"
           /\ LET newPc == [pc EXCEPT ![i] = "l4"]
           IN \/ /\ sem' = sem
              /\ pc' = newPc
        \/ /\ pc[i] = "l4"
           /\ LET newSem == [sem EXCEPT ![i] = 1, ![(i+1) % N] = 1]
              newPc == [pc EXCEPT ![i] = "l1"]
           IN \/ /\ sem' = newSem
              /\ pc' = newPc

Invariant ==
    \A i \in 0..N-1 :
        ~ (pc[i] = "l3" /\ pc[(i+1) % N] = "l3")

StarvationFree ==
    \A i \in 0..N-1 : 
        WF_<<i>>, pc, "l3"

Spec == Init /\ [][Next]_<<sem, pc>> /\ Invariant

=============================================================================