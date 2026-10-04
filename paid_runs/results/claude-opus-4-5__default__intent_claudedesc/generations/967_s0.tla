---------------------------- MODULE BalanceScale ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS W, N

(* Generate all non-decreasing sequences of N positive integers summing to W *)

(* Helper: generate partitions recursively *)
RECURSIVE PartitionsFrom(_, _, _, _)
PartitionsFrom(remaining, parts, minVal, numParts) ==
    IF numParts = 0 
    THEN IF remaining = 0 THEN {parts} ELSE {}
    ELSE IF remaining < minVal * numParts THEN {}
    ELSE LET maxVal == remaining - (numParts - 1)
         IN UNION {PartitionsFrom(remaining - i, Append(parts, i), i, numParts - 1) 
                   : i \in minVal..maxVal}

Partitions == PartitionsFrom(W, <<>>, 1, N)

(* Check if a given weight w can be measured using pieces with coefficients in {-1, 0, 1} *)
RECURSIVE CanMeasure(_, _, _)
CanMeasure(w, parts, idx) ==
    IF idx > Len(parts)
    THEN w = 0
    ELSE \/ CanMeasure(w, parts, idx + 1)                    \* coefficient 0
         \/ CanMeasure(w - parts[idx], parts, idx + 1)       \* coefficient +1
         \/ CanMeasure(w + parts[idx], parts, idx + 1)       \* coefficient -1

(* Check if all weights 1..W can be measured with the given partition *)
CanMeasureAll(parts) ==
    \A w \in 1..W : CanMeasure(w, parts, 1)

(* Find valid partitions *)
ValidPartitions == {p \in Partitions : CanMeasureAll(p)}

(* For TLC to print results *)
PrintResult ==
    IF ValidPartitions # {}
    THEN PrintT(<<"Solution found:", CHOOSE p \in ValidPartitions : TRUE>>)
    ELSE PrintT("No solution")

(* Use ASSUME to trigger evaluation and printing *)
ASSUME PrintResult

(* Minimal spec structure for TLC *)
VARIABLE dummy

Init == dummy = 0

Next == UNCHANGED dummy

Spec == Init /\ [][Next]_dummy

(* Type invariant *)
TypeOK == dummy \in {0}

(* Safety invariant: always true since this is just for computation *)
Safety == TRUE

(* Property capturing that a solution exists (for reference) *)
SolutionExists == ValidPartitions # {}

=============================================================================