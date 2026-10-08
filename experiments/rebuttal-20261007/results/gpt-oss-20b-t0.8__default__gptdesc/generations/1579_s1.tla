MODULE DijkstraRing
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, K

ASSUME N > 0 /\ K > N

VARIABLE x

Idx == 0 .. N-1

Pred(i) == (i - 1 + N) % N

Token(i) == x[i] = ((x[Pred(i)] + 1) Mod K)

(* Initial state: all processes hold arbitrary values in 0..K-1 *)
Init == x \in [Idx -> 0 .. K-1]

(* One step of the algorithm *)
Step ==
    ∨ i \in Idx :
        IF i = 0 THEN
            /\ x[0] = x[Pred(0)]
            /\ x' = [x EXCEPT ![0] = ((x[0] + 1) Mod K)]
        ELSE
            /\ x[i] # x[Pred(i)]
            /\ x' = [x EXCEPT ![i] = x[Pred(i)]]

Next == Step

FairnessCond == WF_Step

Spec == Init /\ [][Next]_<<x>> /\ FairnessCond

(* Safety invariants *)
SomeToken == ∃ i \in Idx : Token(i)

ExactlyOneToken ==
    ∃ i \in Idx :
        (Token(i) /\ ∀ j \in Idx : (j # i => ¬Token(j)))

THEOREM SpecImpliesInvariant_SomeToken == Spec => []SomeToken

THEOREM SpecImpliesEventuallyOneToken == Spec => <>ExactlyOneToken
====================================================================