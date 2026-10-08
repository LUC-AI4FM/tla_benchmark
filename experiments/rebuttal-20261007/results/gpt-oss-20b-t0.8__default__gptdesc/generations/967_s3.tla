---------------------------- MODULE StoneCutting ----------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS W, N \* total weight and number of pieces

PartitionSeq(n,w) ==
  IF n = 0 THEN
    IF w = 0 THEN {<>} ELSE {}
  ELSE
    { Append(seq', <<k>>) : k ∈ 1..w, seq' ∈ PartitionSeq(n-1, w-k) }

WeightedSum(p, coeffs) ==
  Sum({ coeffs[i]*p[i] : i ∈ 1..Len(coeffs) })

Balanced(p) ==
  LET n == Len(p) IN
    ∀ t ∈ 1..W :
      ∃ coeffs \in { s \in Seq(Int) : Len(s)=n /\ (∀ i∈1..n : s[i] ∈ {-1,0,1}) } :
        WeightedSum(p, coeffs) = t

VARIABLE part

Init == part ∈ PartitionSeq(N,W) /\ Balanced(part)

Next == TRUE

Spec == Init /\ [][Next]_vars

SafetyInvariant == Balanced(part)
=============================================================================