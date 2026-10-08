---- MODULE DiningPhilosophers ----

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N

VARIABLES sem, pc

ASSUME N \in Nat /\ N > 1

Init == 
    /\ sem = <<2: Nat>>[N]
    /\ pc = [p \in {0..N-1} -> "think"]

Next ==
    \/ \E p \in {1..N-1} : pc[p] = "think" /\ sem[p] > 0 /\ sem[(p+1) % N] > 0
        /\ sem' = [sem EXCEPT ![p] = sem[p] - 1, ![p+1 \% N] = sem[(p+1) \% N] - 1]
        /\ pc' = [pc EXCEPT ![p] = "eat"]
    \/ \E p \in {1..N-1} : pc[p] = "eat"
        /\ sem' = [sem EXCEPT ![p] = sem[p] + 1, ![p+1 \% N] = sem[(p+1) \% N] + 1]
        /\ pc' = [pc EXCEPT ![p] = "think"]
    \/ pc[0] = "think" /\ sem[0] > 0 /\ sem[N-1] > 0
        /\ sem' = [sem EXCEPT ![0] = sem[0] - 1, ![N-1] = sem[N-1] - 1]
        /\ pc' = [pc EXCEPT ![0] = "eat"]
    \/ pc[0] = "eat"
        /\ sem' = [sem EXCEPT ![0] = sem[0] + 1, ![N-1] = sem[N-1] + 1]
        /\ pc' = [pc EXCEPT ![0] = "think"]

MutualExclusion ==
    \A p \in {0..N-1} : pc[p] # "eat" \/ pc[(p+1) \% N] # "eat"

StarvationFreedom ==
    \A p \in {0..N-1} : <>[]<>(pc[p] = "eat")

Spec ==
    /\ Init
    /\ [][Next]_<<pc, sem>>
    /\ WF_<<pc>>[Next]
    /\ MutualExclusion
    /\ StarvationFreedom

====