MODULE WeightPartition
EXTENDS Naturals, Integers, Sequences

CONSTANTS W, N

VARIABLE pieces

TypeInvariant == pieces \in [1..N -> Nat]

Init ==
    /\ TypeInvariant
    /\ \A i \in 1..N : pieces[i] >= 1
    /\ \sum i \in 1..N : pieces[i] = W

Next ==
    TRUE

AllTargetsAchievable ==
    \A t \in 1..W :
        \E coeff \in [1..N -> {-1,0,1}] :
            \sum i \in 1..N : coeff[i] * pieces[i] = t

Inv == Init /\ AllTargetsAchievable

Spec == Init /\ []Next /\ []Inv

CHECKPOINTS == {pieces}

END MODULE