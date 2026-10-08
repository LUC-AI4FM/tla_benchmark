------------------------------ MODULE DijkstraRing ------------------------------
EXTENDS Naturals, Sequences, TLC, Fairness

CONSTANTS N, M

ASSUME N >= 2
ASSUME M >= 1
ASSUME N <= M + 1

VARIABLE x

(* Initial state: arbitrary counter values in the domain *)
Init == /\ x \in [0 .. N-1 -> 0 .. M-1]

Pred(i) == IF i = 0 THEN N-1 ELSE i - 1

Priv(i) == x[i] # x[Pred(i)]

Action_0 ==
    /\ Priv(0)
    /\ x' = [x EXCEPT ![0] = ((x[0] + 1) Mod M)]

Action_i(i) ==
    /\ i \in 1 .. N-1
    /\ Priv(i)
    /\ x' = [x EXCEPT ![i] = x[Pred(i)] ]

Next == Action_0 \/ \E i \in 1..N-1 : Action_i(i)

OneToken ==
    \E i \in 0 .. N-1 :
        /\ (x[i] # x[Pred(i)])
        /\ \A j \in 0 .. N-1 : (j /= i) => ~(x[j] # x[Pred(j)])

Spec == Init /\ [][Next]_x /\ WF_1(Next)

Stabilization == <>[]OneToken

THEOREM StabilizationThm: Spec => Stabilization
=============================================================================