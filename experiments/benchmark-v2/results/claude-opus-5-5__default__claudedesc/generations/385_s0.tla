---------------------------- MODULE test216 ----------------------------
EXTENDS Naturals

---------------------------- MODULE test216a ----------------------------
CONSTANT D
VARIABLE x

DVal == D

THEOREM Thm == D \in Nat

LEMMA Lem == DVal = D

PropA == []<>(x < D)
=========================================================================