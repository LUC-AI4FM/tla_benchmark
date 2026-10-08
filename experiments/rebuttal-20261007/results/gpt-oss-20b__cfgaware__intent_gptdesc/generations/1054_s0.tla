MODULE TokenRing

CONSTANTS N, M, Source

ASSUME
    /\ 1 <= Source <= N
    /\ 2 <= M

VARIABLE C

(* Helper function for predecessor in ring *)
Pred(i) == IF i = 1 THEN N ELSE i - 1

Init ==
    /\ C \in [i \in 1..N -> 0 .. M-1]

Inject ==
    /\ C' = [C EXCEPT ![Source] = (C[Source] + 1) Mod M]

Copy(i) ==
    /\ i \in 1..N
    /\ i #= Source
    /\ C[i] #= C[Pred(i)]
    /\ C' = [C EXCEPT ![i] = C[Pred(i)]]

Next == Inject \/ \E i \in 1..N : Copy(i)

vars == {C}

Spec ==
    Init
    /\ [][Next]_vars
    /\ Fairness

Fairness ==
    WF(Inject)
    /\ \E i \in 1..N : WF(Copy(i))

Safety ==
    \A i \in 1..N : C[i] \in 0 .. M-1

Canonical(v) ==
    /\ v \in 0 .. M-1
    /\