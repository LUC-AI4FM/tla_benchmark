---------------------------- MODULE BalanceScale ----------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS W, N

(*
  PosNat: positive naturals
*)
PosNat == Nat \ {0}

(*
  Recursive sum of a sequence of integers
*)
RECURSIVE SumSeq(_)
SumSeq(s) ==
  IF Len(s) = 0 THEN 0
  ELSE Head(s) + SumSeq(Tail(s))

(*
  Recursive enumeration of ordered partitions of w into n positive parts.
  Returns a set of sequences of length n over PosNat whose elements sum to w.
*)
RECURSIVE Partitions(_, _)
Partitions(w, n) ==
  IF n = 0 THEN
    IF w = 0 THEN { << >> } ELSE {}
  ELSE
    LET MaxK == w - (n - 1) IN
      UNION { { <<k>> \o r : r \in Partitions(w - k, n - 1) } : k \in 1..MaxK }

(*
  Recursive enumeration of coefficient vectors of length n over {-1, 0, 1}
*)
RECURSIVE Coefs(_)
Coefs(n) ==
  IF n = 0 THEN { << >> }
  ELSE { <<c>> \o r : c \in {-1, 0, 1}, r \in Coefs(n - 1) }

(*
  Dot product using SumSeq
*)
Dot(w, c) == SumSeq([ i \in 1..Len(w) |-> w[i] * c[i] ])

(*
  Weighability: can we represent target t using coefficients in {-1,0,1}?
*)
Weighable(w, t) == \E co \in Coefs(Len(w)) : Dot(w, co) = t

(*
  BalancedAll: every target in 1..W is representable
*)
BalancedAll(w) == \A t \in 1..W : Weighable(w, t)

(*
  All solutions (ordered partitions) satisfying BalancedAll
*)
Solutions == { w \in Partitions(W, N) : BalancedAll(w) }

(*
  A representative solution if one exists, else the empty sequence
*)
Solution == IF Solutions # {} THEN CHOOSE w \in Solutions : TRUE ELSE << >>

(*
  TLC-oriented printing to show search results
*)
ASSUME W \in PosNat /\ N \in PosNat /\ N <= W
ASSUME PrintT(<<"Searching balance-scale partitions", [W |-> W, N |-> N]>>) = TRUE
ASSUME PrintT(<<"NumberOfSolutions", Cardinality(Solutions)>>) = TRUE
ASSUME PrintT(IF Solutions # {} THEN <<"OneSolution", Solution>> ELSE <<"NoSolution">>) = TRUE

VARIABLES weights

Init ==
  /\ weights \in Partitions(W, N)
  /\ BalancedAll(weights)

Next ==
  UNCHANGED weights

Spec ==
  Init /\ [][Next]_<<weights>>

(*
  Safety invariants capturing the problem requirements
*)
TypeInv ==
  /\ weights \in Seq(PosNat)
  /\ Len(weights) = N
  /\ SumSeq(weights) = W

BalanceInv ==
  BalancedAll(weights)

SafetyInv == TypeInv /\ BalanceInv
============================================================================