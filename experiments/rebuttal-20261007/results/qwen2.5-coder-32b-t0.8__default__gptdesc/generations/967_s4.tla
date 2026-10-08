------------------------------- MODULE StoneCutting -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS W, N

VARIABLES weights

Init == /\ weights \in Seq(Naturals)
        /\ Len(weights) = N
        /\ Sum(weights) = W
        /\ \A i \in 1..N : weights[i] > 0

Next == CHOOSE newWeights \in [1..N -> Naturals] :
              \/ /\ Sum(newWeights) = W
                 /\ \A i \in 1..N : newWeights[i] > 0
                 /\ \/ \E seq \in PossiblePartitions(N, weights) : CanWeighAll(seq)
                    \/ ~\E seq \in PossiblePartitions(N, newWeights) : CanWeighAll(seq)

PossiblePartitions(n, seq) == 
    IF n = 1 THEN {[<<seq[1]>>]}
    ELSE {s \o <<e>> \in Seq(PossiblePartitions(n-1, seq)) X {0..Sum(take(seq, n))}
         : Sum(s) + e <= Sum(take(seq, n))}

take(seq, n) == <<seq[i] : i \in 1..n>>

CanWeighAll(partition) ==
    \A target \in 1..W : \E coeffs \in [1..Len(partition) -> {-1, 0, 1}] :
        Sum({coeffs[i] * partition[i] : i \in 1..Len(partition)}) = target

Spec == Init /\ [][Next]_<<weights>>

Assume Spec
PrintT(weights)
 fairness
    WF_vars(<<weights>>, Next)

=============================================================================