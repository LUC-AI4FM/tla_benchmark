---------------------------- MODULE CarTalkPuzzle ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS W, N

(* Helper function to compute the sum of elements in a sequence *)
RECURSIVE SeqSum(_)
SeqSum(seq) ==
    IF seq = << >> THEN 0
    ELSE Head(seq) + SeqSum(Tail(seq))

(* Recursively enumerate all non-decreasing sequences of N natural numbers that sum to W *)
(* seq: current partial sequence, wt: remaining weight to distribute *)
RECURSIVE Partitions(_, _)
Partitions(seq, wt) ==
    LET len == Len(seq)
        remaining == N - len
    IN
    IF remaining = 0 THEN
        IF wt = 0 THEN {seq} ELSE {}
    ELSE
        LET minVal == IF len = 0 THEN 1 ELSE seq[len]
            (* Each remaining piece must be at least minVal, so max for current piece *)
            maxVal == IF remaining > 0 THEN wt - (remaining - 1) * minVal ELSE wt
        IN
        IF minVal > maxVal THEN {}
        ELSE
            UNION {Partitions(Append(seq, v), wt - v) : v \in minVal..maxVal}

(* Check whether a given partition can represent a target weight wt *)
(* by existentially quantifying over coefficient assignments from {-1, 0, 1} *)
Weighs(seq, wt) ==
    LET Coeffs == {-1, 0, 1}
        (* All possible coefficient sequences of length N *)
        CoeffSeqs == [1..Len(seq) -> Coeffs]
        (* Compute the weighted sum for a coefficient sequence *)
        WeightedSum(coeffs) == SeqSum([i \in 1..Len(seq) |-> coeffs[i] * seq[i]])
    IN
    \E coeffs \in CoeffSeqs : WeightedSum(coeffs) = wt

(* Check if a partition can measure all weights from 1 to W *)
CanMeasureAll(seq) ==
    \A target \in 1..W : Weighs(seq, target)

(* Find and print solutions *)
Solutions ==
    LET allPartitions == Partitions(<< >>, W)
        validPartitions == {p \in allPartitions : CanMeasureAll(p)}
    IN
    IF validPartitions = {} THEN
        PrintT("No solution")
    ELSE
        \A p \in validPartitions : PrintT(p)

ASSUME Solutions

=============================================================================