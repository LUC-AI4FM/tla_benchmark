----------------------------- MODULE RecFunInvariant -----------------------------

EXTENDS Naturals, Integers

CONSTANT N

ASSUME N \in Nat /\ N <= 10

VARIABLE x

Dom == 0..N

RECURSIVE Tri(_)
Tri(n) ==
  IF n = 0 THEN 0
  ELSE IF n \in 1..N THEN Tri(n - 1) + n
  ELSE 0

SeqFun == [n \in Dom |-> Tri(n)]

RangeSeq == { SeqFun[n] : n \in Dom }

Init == x \in RangeSeq

Next == UNCHANGED x

Inv == x \in RangeSeq

Spec == Init /\ [][Next]_x

THEOREM Spec => []Inv

===============================================================================