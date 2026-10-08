------------------------------ MODULE DijkstraRing ------------------------------
EXTENDS Naturals

CONSTANTS N, M

VARIABLE V

(* --- Definitions ----------------------------------------------------------- *)
Domain     == 0 .. M - 1
NodeIdx    == 0 .. N - 1

Prev(i)    == IF i = 0 THEN N - 1 ELSE i - 1

NextVal(x) == (x + 1) MOD M

(* --- Initial State -------------------------------------------------------- *)
Init ==
    /\ V \in [NodeIdx -> Domain]

(* --- Transition Actions --------------------------------------------------- *)
Node0Inc ==
    /\ V[0] #= V[N-1]
    /\ V' = [V EXCEPT ![0] = NextVal(V[N-1])]

NodeCopy(i) ==
    /\ i ∈ NodeIdx \ {0}
    /\ V[i] #= V[Prev(i)]
    /\ V' = [V EXCEPT ![i] = V[Prev(i)]]

Next == Node0Inc \/ (∃i ∈ NodeIdx \ {0} : NodeCopy(i))

(* --- Specification -------------------------------------------------------- *)
Spec == Init /\ [][Next]_V

(* --- Safety Invariants ---------------------------------------------------- *)
AllValuesInDomain ==
    ∀i ∈ NodeIdx : V[i] ∈ Domain

(* --- Liveness Property (Stabilization) ----------------------------------- *)
UniqueTokenState ==
    ∃i ∈ NodeIdx, t ∈ Domain, u ∈ Domain :
        (t #= u) /\ (V[i] = t) /\ (∀j ∈ NodeIdx \ {i} : V[j] = u)

Stabilization == ◇□ UniqueTokenState

(* --- End of Module -------------------------------------------------------- *)
=============================================================================