```tla
MODULE DiningPhilosophers

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N

VARIABLES sem, pc

ASSUME N \in Nat \ {0}

Init == /\ sem = <<1, 1, ..., 1>>  \o [1..N -> 0]
        /\ pc = [p \in 0..N-1 |-> "think"]

Next ==
    \/ \E p \in 0..N-1 : 
        (\A q \in (p+1)%N..(p+N-2)%N: pc[q] /= "eat") /\ 
        (pc[p] = "think" -> 
            (p # 0 -> 
                /\ sem[(p+1)%N] > 0
                /\ sem[p] > 0
                /\ sem'[(p+1)%N] = sem[(p+1)%N] - 1
                /\ sem'[p] = sem[p] - 1
            \/ p = 0 ->
                /\ sem[p] > 0
                /\ sem[(p+N-1)%N] > 0
                /\ sem'[p] = sem[p] - 1
                /\ sem'[(p+N-1)%N] = sem[(p+N-1)%N] - 1)
            /\ pc'[p] = "eat"
            /\ (\A q \in 0..N-1 \ {p}: pc'[q] = pc[q]))
    \/ \E p \in 0..N-1 : 
        (pc[p] = "eat" ->
            /\ sem'[(p+1)%N] = sem[(p+1)%N] + 1
            /\ sem'[p] = sem[p] + 1
            /\ pc'[p] = "think"
            /\ (\A q \in 0..N-1 \ {p}: pc'[q] = pc[q]))

Spec ==
    /\ Init
    /\ [][Next]_<<pc, sem>>
    /\ WF_next(<<pc, sem>>)

MutualExclusion == 
    \A p, q \in 0..N-1 : p # q => ~ (pc[p] = "eat" /\ pc[q] = "eat" /\ (q = (p+1)%N \/ q = (p+N-1)%N))

StarvationFreedom ==
    \A p \in 0..N-1 : <>[][pc[p] = "eat"]_<<pc, sem>>

INVARIANT MutualExclusion

TEMPORAL StarvationFreedom
```