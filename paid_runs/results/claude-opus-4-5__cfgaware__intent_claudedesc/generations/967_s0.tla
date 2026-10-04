---------------------------- MODULE puzzle ----------------------------

EXTENDS Integers, Sequences, TLC

CONSTANTS W, N

(* Generate all non-decreasing sequences of N positive integers that sum to W *)
RECURSIVE PartitionsFrom(_, _, _, _)
PartitionsFrom(remaining, count, minVal, prefix) ==
    IF count = 0
    THEN IF remaining = 0 THEN {prefix} ELSE {}
    ELSE IF remaining < count * minVal
         THEN {}
         ELSE UNION {PartitionsFrom(remaining - v, count - 1, v, Append(prefix, v)) 
                     : v \in minVal..remaining - (count - 1)}

Partitions == PartitionsFrom(W, N, 1, <<>>)

(* Check if a given weight w can be measured using pieces from partition p *)
(* Each piece can contribute +1, -1, or 0 times its weight *)
RECURSIVE CanMeasure(_, _, _)
CanMeasure(target, p, idx) ==
    IF idx > Len(p)
    THEN target = 0
    ELSE \/ CanMeasure(target - p[idx], p, idx + 1)  \* piece on opposite side (+)
         \/ CanMeasure(target + p[idx], p, idx + 1)  \* piece on same side as unknown (-)
         \/ CanMeasure(target, p, idx + 1)           \* piece not used (0)

(* Check if partition p can measure all weights from 1 to W *)
CanMeasureAll(p) ==
    \A w \in 1..W : CanMeasure(w, p, 1)

(* Find all valid partitions *)
ValidPartitions == {p \in Partitions : CanMeasureAll(p)}

(* Convert sequence to string for printing *)
RECURSIVE SeqToString(_)
SeqToString(s) ==
    IF s = <<>> THEN ""
    ELSE IF Len(s) = 1 THEN ToString(Head(s))
         ELSE ToString(Head(s)) \o ", " \o SeqToString(Tail(s))

(* Find one valid partition if it exists *)
Solution ==
    IF ValidPartitions # {}
    THEN CHOOSE p \in ValidPartitions : TRUE
    ELSE <<>>

(* Print result via assumption *)
ASSUME
    IF ValidPartitions # {}
    THEN PrintT(<<"Valid partition found:", Solution>>)
    ELSE PrintT("No solution")

=======================================================================