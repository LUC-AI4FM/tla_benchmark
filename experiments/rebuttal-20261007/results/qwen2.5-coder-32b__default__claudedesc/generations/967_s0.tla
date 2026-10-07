------------------------------- MODULE CarTalkPuzzle -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS W, N

ASSUME W \in Nat /\ W > 0
ASSUME N \in Nat /\ N > 0

Partitions(seq, wt) == 
    IF seq = <<>> THEN 
        { s \in [1..N -> Nat] : Sum(s) = wt }
    ELSE
        LET last = Last(seq)
            min = IF Cardinality(seq) < N THEN 0 ELSE last
            max = wt - (Sum(seq) - last)
        IN
        UNION { Partitions(Append(seq, i), wt) : i \in min..max }

Weighs(seq, wt) ==
    LET coeffs == [1..Cardinality(seq)] -> {-1, 0, 1}
    IN
    \E c \in coeffs : Sum({ j * seq[i] : i \in DOMAIN seq }) = wt

ASSUME 
    LET partitions == Partitions(<<>>, W)
        validPartition == CHOOSE p \in partitions : \A w \in 1..W : Weighs(p, w)
    IN
    IF partitions /= {} THEN PrintT(validPartition) ELSE PrintT("No solution")

Init == TRUE

Next == FALSE

Spec == Init /\ []Next
=============================================================================