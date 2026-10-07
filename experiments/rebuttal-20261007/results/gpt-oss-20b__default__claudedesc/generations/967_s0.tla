MODULE CarTalkPuzzle
EXTENDS Naturals, Sequences, TLC

CONSTANTS W, N
(* Default values: W = 40, N = 4 *)

RecPartitions(k, rem, minVal) ==
   IF k = 0 THEN
        IF rem = 0 THEN { <> } ELSE {}
   ELSE
        { first \o rest :
            first \in minVal .. (rem \div k) /\ 
            rest \in RecPartitions(k-1, rem-first, first) }

Partitions(seq, wt) == RecPartitions(N, W, 1)

Weighs(seq, wt) ==
   LET coeffSet == { c \in Seq(N) : ∀ i \in 1..N : c[i] \in {-1,0,1} } IN
       ∃ c \in coeffSet : (SUM i \in 1..N : c[i]*seq[i]) = wt

ASSUME
   LET seqs == Partitions(0,0) IN
   IF ∃ s \in seqs : ∀ w \in 1..W : Weighs(s,w)
   THEN PrintT("Solution found: ", SOME s \in seqs : ∀ w \in 1..W : Weighs(s,w))
   ELSE PrintT("No solution")

VARIABLES dummy

Init == TRUE
Next == dummy' = dummy

Spec == Init /\ []Next

END MODULE