------------------------------- MODULE DiningPhilosophers -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N \* Number of philosophers
ASSUME N \in Nat /\ N > 0

VARIABLES sem, pc

vars == <<sem, pc>>

Init == 
    /\ sem = <<1>> ^ N
    /\ pc = [p \in 0..N-1 |-> "think"]

Next ==
    \/ \E p \in 0..N-1 : 
        (pc[p] = "think" /\ sem[p] = 1 /\ sem[(p-1) % N] = 1
         -> /\ pc' = [pc EXCEPT ![p] = "eat"]
            /\ sem' = [sem EXCEPT ![p] = 0, ![(p-1) % N] = 0])
    \/ \E p \in 0..N-1 : 
        (pc[p] = "eat"
         -> /\ pc' = [pc EXCEPT ![p] = "think"]
            /\ sem' = [sem EXCEPT ![p] = 1, ![(p-1) % N] = 1])

Invariant ==
    \A p \in 0..N-1 : 
        (pc[p] = "eat" => pc[(p+1) % N] # "eat")

StarvationFree ==
    \A p \in 0..N-1 :
        WF_vars(<<p>>, pc' = [pc EXCEPT ![p] = "eat"])

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Invariant
    /\ StarvationFree

=============================================================================