MODULE BalanceScalePuzzle

IMPORTS Integers

CONSTANTS W, N

(* Empty sequence used to indicate that no solution exists *)
NoSolution == <<>>

VARIABLE result

(* All non‑decreasing partitions of W into N positive integers *)
AllPartitions ==
  { p \in [1..N -> Nat] :
      /\ \A i \in 1..N : p[i] >= 1
      /\ \A i \in 1..N-1 : p[i] <= p[i+1]
      /\ SUM i \in 1..N : p[i] = W }

(* Set of all signed sums that can be obtained from a partition p *)
SignedSums(p) ==
  { SUM i \in 1..N : c[i]*p[i] :
      c \in [1..N -> {-1,0,1}] }

(* A partition is measurable if every integer weight 1..W can be expressed
   as a signed sum of its parts. *)
Measurable(p) == (1..W) \subseteq SignedSums(p)

Init == result = NoSolution

Next ==
  LET Exists == \E p \in AllPartitions : Measurable(p)
      Pick   == CHOOSE p \in AllPartitions : Measurable(p)
  IN
    result' = IF Exists THEN Pick ELSE NoSolution

Inv ==
  (result = NoSolution) \/ (result \in AllPartitions /\ Measurable(result))

Spec == Init /\ [][Next]_result

THEOREM Spec => Inv

END MODULE