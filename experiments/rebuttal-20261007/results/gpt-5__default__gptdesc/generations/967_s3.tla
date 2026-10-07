---- MODULE BalanceScale ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS W, N

VARIABLES pcs

(*
  Natural-number pieces are strictly positive.
*)
Nat1 == Nat \ {0}

RECURSIVE SumSeq(_)
SumSeq(s) ==
  IF Len(s) = 0 THEN 0 ELSE Head(s) + SumSeq(Tail(s))

RECURSIVE Dot(_, _)
Dot(c, p) ==
  IF Len(c) = 0 THEN 0 ELSE Head(c) * Head(p) + Dot(Tail(c), Tail(p))

RECURSIVE Coeffs(_)
Coeffs(n) ==
  IF n = 0 THEN {<< >>}
  ELSE { Append(s, k) : s \in Coeffs(n - 1), k \in {-1, 0, 1} }

RECURSIVE OrderedParts(_, _)
OrderedParts(t, n) ==
  IF n = 0 THEN IF t = 0 THEN {<< >>} ELSE {}
  ELSE { Append(s, k) : k \in 1..t, s \in OrderedParts(t - k, n - 1) }

BalancedForTarget(p, t) ==
  \E c \in Coeffs(Len(p)) : Dot(c, p) = t

BalancedAll(p) ==
  \A t \in 1..W : BalancedForTarget(p, t)

TypeOK ==
  pcs \in Seq(Nat1) /\ Len(pcs) = N

SumOK ==
  SumSeq(pcs) = W

Init ==
  pcs \in OrderedParts(W, N)

Next ==
  UNCHANGED pcs

Spec ==
  Init /\ [][Next]_pcs

ASSUME W \in Nat /\ N \in Nat

ASSUME
  LET Sols == { p \in OrderedParts(W, N) : BalancedAll(p) }
  IN IF Sols # {}
     THEN PrintT(<<"Found solution (W =", W, ", N =", N, "): ", CHOOSE p \in Sols : TRUE>>)
     ELSE PrintT(<<"No solution exists for W =", W, " and N =", N>>)

====