---- MODULE CarTalkBalance ----
EXTENDS Integers, Sequences, TLC

CONSTANTS W, N

RECURSIVE Partitions(_, _)
Partitions(pfx, rem) ==
  LET l == Len(pfx) IN
  LET r == N - l IN
  IF r = 0 THEN
    IF rem = 0 THEN {pfx} ELSE {}
  ELSE IF rem <= 0 THEN
    {}
  ELSE
    LET nextMin == IF l = 0 THEN 1 ELSE pfx[l] IN
    LET nextMax == rem \div r IN
    IF nextMin > nextMax THEN
      {}
    ELSE
      UNION { Partitions(Append(pfx, x), rem - x) : x \in nextMin..nextMax }

RECURSIVE SumSeq(_)
SumSeq(s) ==
  IF Len(s) = 0 THEN 0 ELSE Head(s) + SumSeq(Tail(s))

Weighs(seq, wt) ==
  LET n == Len(seq) IN
  \E coef \in [1..n -> {-1, 0, 1}] :
    SumSeq([i \in 1..n |-> coef[i] * seq[i]]) = wt

ASSUME
  LET parts == Partitions(<<>>, W),
      Valid(s) == \A w \in 1..W: Weighs(s, w),
      sols == { s \in parts : Valid(s) }
  IN IF sols # {} THEN
       PrintT(<<"Solution", CHOOSE s \in sols: TRUE>>)
     ELSE
       PrintT("No solution")

====