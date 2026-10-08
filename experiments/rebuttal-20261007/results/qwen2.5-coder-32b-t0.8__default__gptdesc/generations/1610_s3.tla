------------------------------- MODULE QuicksortSpec -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES pc, arr, S

Init == 
  /\ pc = "qs1"
  /\ arr \in [1..N -> 1..N]
  /\ S = {<<1, N>>}

Next ==
  (pc = "qs1" /\ <<lo, hi>> \in S
   -> \/ /\ <<lo', hi'>> \in {<<lo+1, hi>>, <<lo, hi-1>>, <<lo, lo>>, <<hi, hi>>}
          /\ S' = (S \ {<<lo, hi>>}) \cup (IF lo < hi THEN {<<lo', hi'>>} ELSE {})
          /\ pc' = IF lo >= hi THEN "Done" ELSE "qs1"
          /\ arr' \in [arr EXCEPT !![i \in lo..hi |-> 
             CHOOSE x \in {arr[i] : i \in lo..hi} :
               (FORALL y \in {arr[j] : j \in lo..(lo'-1)}: x <= y)
               /\ (FORALL y \in {arr[j] : j \in (hi'+1)..hi}: x >= y)]
      )

Spec ==
  /\ Init
  /\ [][Next]_<<pc, arr, S>>
  /\ WF_next(<<pc, arr, S>>)

Termination == <>[](pc = "Done")

=============================================================================