```tla
MODULE BalanceScale

EXTENDS Integers, TLC

CONSTANTS W, N

VARIABLES pieces, target, coefficients, sums

Init == 
  /\ pieces = << >>
  /\ target = 1
  /\ coefficients = << >>
  /\ sums = << >>

Next == 
  IF target <= W THEN
    /\ pieces' = 
      IF << >> \in [1..W] @ [1..N] 
      THEN Append(pieces, CHOOSE x \in Nat : x <= W)
      ELSE pieces
    /\ target' = target + 1
    /\ coefficients' = 
      IF << >> \in [1..W] @ [1..N] 
      THEN Append(coefficients, CHOOSE c \in {-1, 0, 1} : TRUE)
      ELSE coefficients
    /\ sums' = Append(sums, SumSeq(coefficients, pieces))
  ELSE 
    /\ pieces' = pieces
    /\ target' = target
    /\ coefficients' = coefficients
    /\ sums' = sums

SumSeq(seq, nums) == 
  IF seq = << >> THEN 0
  ELSE LET h == Head(seq), t == Tail(seq), n == Head(nums)
  IN h * n + SumSeq(t, Tail(nums))

Spec == Init /\ [][Next]_pieces

THEOREM Spec => []<>target > W

INVARIANT pieces \in Seq(Nat)
INVARIANT target \in Nat
INVARIANT coefficients \in Seq(-1..1)
INVARIANT sums \in Seq(Int)

Fairness == <>[]target > W

ASSUME PrintT("Solution found: ") /\ pieces # << >> /\ target = W + 1

ASSUME PrintT("No solution exists.") /\ [](target' = target) /\ target = W
```