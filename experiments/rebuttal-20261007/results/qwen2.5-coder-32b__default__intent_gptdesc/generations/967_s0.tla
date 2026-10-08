------------------------------- MODULE WeighingPieces -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS W, N

VARIABLES pieces

Init == /\ pieces \in [1..N -> 1..W]
        /\ Sum(pieces) = W
        /\ (\A i \in 1..N : pieces[i] > 0)

Next == FALSE

Spec == Init /\ [][\E<<>> \in ([-1..1]^(1..N)) : 
                    \A t \in 1..W : 
                        \E coeffs \in [-1..1]^(1..N) : 
                            Sum({i \in 1..N : coeffs[i] = -1} -> pieces) + t = 
                            Sum({i \in 1..N : coeffs[i] = 1} -> pieces)]

Invariant1 == Sum(pieces) = W

Invariant2 == (\A i \in 1..N : pieces[i] > 0)

Invariant3 == (\A t \in 1..W : 
                    \E coeffs \in [-1..1]^(1..N) : 
                        Sum({i \in 1..N : coeffs[i] = -1} -> pieces) + t = 
                        Sum({i \in 1..N : coeffs[i] = 1} -> pieces))

Spec == Spec /\ []Invariant1 /\ []Invariant2 /\ []Invariant3

=============================================================================