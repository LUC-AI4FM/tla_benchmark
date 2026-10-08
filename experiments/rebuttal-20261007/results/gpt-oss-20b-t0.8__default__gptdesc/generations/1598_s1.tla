MODULE FastMutualExclusion
EXTENDS Naturals, TLC

CONSTANT N \in Nat

VARIABLES x, y, b, S, cs

vars == <<x, y, b, S, cs>>

AllIndices == 1..N

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i ∈ AllIndices |-> FALSE]
    /\ S = [i ∈ AllIndices |-> {}]
    /\ cs = [i ∈ AllIndices |-> FALSE]

StartAttempt(i) ==
    /\ i ∈ AllIndices
    /\ b[i] = FALSE
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<x, y, S, cs>>

SetX(i) ==
    /\ i ∈ AllIndices
    /\ b[i] = TRUE
    /\ x' = i
    /\ UNCHANGED <<b, y, S, cs>>

SetY(i) ==
    /\ i ∈ AllIndices
    /\ b[i] = TRUE
    /\ y' = i
    /\ UNCHANGED <<b, x, S, cs>>

EnterCritical(i) ==
    /\ i ∈ AllIndices
    /\ b[i] = TRUE
    /\ x = i
    /\ y = i
    /\ cs' = [cs EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<b, x, y, S>>

ExitCritical(i) ==
    /\ i ∈ AllIndices
    /\ cs[i] = TRUE
    /\ cs' = [cs EXCEPT ![i] = FALSE]
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ y' = 0
    /\ UNCHANGED <<x, S>>

Next ==
    \/ ∃ i ∈ AllIndices : StartAttempt(i)
    \/ ∃ i ∈ AllIndices : SetX(i)
    \/ ∃ i ∈ AllIndices : SetY(i)
    \/ ∃ i ∈ AllIndices : EnterCritical(i)
    \/ ∃ i ∈ AllIndices : ExitCritical(i)

MutualExclusion ==
    ∀ i, j ∈ AllIndices :
        (i # j) => ~(cs[i] /\ cs[j])

InfinitelyOftenCS == □◇ (∃ i ∈ AllIndices : cs[i])

Spec ==
    Init
    /\ [][Next]_vars
    \/ WF_vars(Next)

Safety ==
    MutualExclusion

Liveness ==
    InfinitelyOftenCS

END MODULE