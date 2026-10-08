------------------------------ MODULE DiningPhilosophers ------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 1

VARIABLES pc, sem

Init == 
    /\ pc = <<0>> :> [i \in {0..N-1} |-> "think"]
    /\ sem = [f \in {0..N-1} |-> TRUE]

RightFork(i) == i
LeftFork(i)  == (i - 1) % N

Pickup(i) ==
    \/ /\ pc[i] = "think"
       /\ sem[RightFork(i)]
       /\ sem[LeftFork(i)]
       /\ sem' = [sem EXCEPT ![RightFork(i)] = FALSE, ![LeftFork(i)] = FALSE]
       /\ pc' = [pc EXCEPT ![i] = "eat"]
    \/ /\ pc[i] = "think"
       /\ sem[RightFork(i)]
       /\ ~ sem[LeftFork(i)]
       /\ sem' = [sem EXCEPT ![RightFork(i)] = FALSE]
       /\ pc' = [pc EXCEPT ![i] = "wait_left"]
    \/ /\ pc[i] = "think"
       /\ ~ sem[RightFork(i)]
       /\ sem' = [sem EXCEPT ![RightFork(i)] = FALSE]
       /\ pc' = [pc EXCEPT ![i] = "wait_right"]

WaitLeft(i) ==
    \/ /\ pc[i] = "wait_left"
       /\ sem[LeftFork(i)]
       /\ sem' = [sem EXCEPT ![LeftFork(i)] = FALSE]
       /\ pc' = [pc EXCEPT ![i] = "eat"]
    \/ /\ pc[i] = "wait_left"
       /\ ~ sem[LeftFork(i)]
       /\ pc' = [pc EXCEPT ![i] = "wait_left"]

WaitRight(i) ==
    \/ /\ pc[i] = "wait_right"
       /\ sem[RightFork(i)]
       /\ sem' = [sem EXCEPT ![RightFork(i)] = FALSE]
       /\ pc' = [pc EXCEPT ![i] = "wait_left"]
    \/ /\ pc[i] = "wait_right"
       /\ ~ sem[RightFork(i)]
       /\ pc' = [pc EXCEPT ![i] = "wait_right"]

Eat(i) ==
    \/ /\ pc[i] = "eat"
       /\ pc' = [pc EXCEPT ![i] = "think"]
       /\ sem' = [sem EXCEPT ![RightFork(i)] = TRUE, ![LeftFork(i)] = TRUE]
    \/ /\ pc[i] = "eat"
       /\ pc' = [pc EXCEPT ![i] = "eat"]

PhilAction(i) ==
    \/ i # 0 -> Pickup(i)
    \/ i = 0 -> 
        (\/ /\ pc[i] = "think"
             /\ sem[LeftFork(i)]
             /\ sem[RightFork(i)]
             /\ sem' = [sem EXCEPT ![LeftFork(i)] = FALSE, ![RightFork(i)] = FALSE]
             /\ pc' = [pc EXCEPT ![i] = "eat"]
         \/ /\ pc[i] = "think"
              /\ sem[LeftFork(i)]
              /\ ~ sem[RightFork(i)]
              /\ sem' = [sem EXCEPT ![LeftFork(i)] = FALSE]
              /\ pc' = [pc EXCEPT ![i] = "wait_right"]
         \/ /\ pc[i] = "think"
              /\ ~ sem[LeftFork(i)]
              /\ pc' = [pc EXCEPT ![i] = "wait_left"])
    \/ WaitLeft(i)
    \/ WaitRight(i)
    \/ Eat(i)

Next ==
    \E i \in {0..N-1} : PhilAction(i) /\ \A j \in {0..N-1} \ {i} : pc' [j] = pc[j] /\ sem' [j] = sem[j]

Spec == Init /\ [][Next]_<<pc, sem>>

Invariant ==
    \A i \in {0..N-1} :
        \/ pc[i] # "eat"
        \/ (pc[(i - 1) % N] # "eat" /\ pc[(i + 1) % N] # "eat")

StarvationFreeness ==
    \A p \in {0..N-1} : WF_<<pc, sem>>(p)

=============================================================================