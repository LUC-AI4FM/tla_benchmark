---------------------------- MODULE BalanceScale ----------------------------
EXTENDS Integers

CONSTANT W, N

VARIABLE pieces, targetWeight

Init == (pieces = <<>>) /\
        (targetWeight = 1)

Weigh(pieces, weight) ==
  IF weight = 0 THEN TRUE
  ELSE \E i \in 1..Len(pieces) :
       Weigh(<<>>, weight - pieces[i]) \*
       (pieces[i] # 0)

CanBalance(pieces, targetWeight) ==
  \E coeffs \in [1..Len(pieces) -> {-1, 0, 1}] :
    Sum(coeffs \* pieces) = targetWeight

Sum(seq) == IF seq = <<>> THEN 0 ELSE Head(seq) + Sum(Tail(seq))

Partition(n, w) ==
  IF n = 0 THEN <<>>
  ELSE \E p \in Nat :
       (p <= w /\ Partition(n - 1, w - p) # <<>>) /\
       <<p>> \o Partition(n - 1, w - p)

Next == \E newPieces \in [Partition(N, W)] :
          CanBalance(newPieces, targetWeight) /\
          pieces' = newPieces /\
          IF targetWeight < W THEN targetWeight' = targetWeight + 1
          ELSE targetWeight' = targetWeight

Spec == Init /\ [][Next]_pieces

THEOREM Spec => []CanBalance(pieces, W)

ASSUME W > 0 /\ N > 0

PrintT == IF CanBalance(pieces, W) THEN "Solution found: " \o SeqToString(pieces)
         ELSE "No solution exists"

=============================================================================