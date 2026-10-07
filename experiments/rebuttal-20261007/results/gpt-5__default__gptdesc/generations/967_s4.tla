---- MODULE BalanceScale ----
EXTENDS Integers, Sequences, TLC

CONSTANTS
  W, \* Total weight (a natural number)
  N  \* Number of pieces (a natural number)

VARIABLES
  pieces \* Chosen ordered partition (sequence) of piece weights

NatPlus == Nat \ {0}
CoeffDomain == {-1, 0, 1}

RECURSIVE SumSeq(_)
SumSeq(s) ==
  IF Len(s) = 0 THEN 0 ELSE Head(s) + SumSeq(Tail(s))

RECURSIVE AllSeqs(_, _)
AllSeqs(S, n) ==
  IF n = 0 THEN { << >> }
  ELSE { Append(seq, x) : seq \in AllSeqs(S, n - 1), x \in S }

RECURSIVE Partitions(_, _)
Partitions(n, w) ==
  IF n = 0 THEN
    IF w = 0 THEN { << >> } ELSE {}
  ELSE
    { Append(p, k) : k \in 1..w, p \in Partitions(n - 1, w - k) }

RECURSIVE Dot(_, _)
Dot(c, p) ==
  IF Len(c) = 0 THEN 0
  ELSE Head(c) * Head(p) + Dot(Tail(c), Tail(p))

Balanced(p, t) ==
  LET n == Len(p) IN
    \E c \in AllSeqs(CoeffDomain, n) : Dot(c, p) = t

BalancedAll(p) ==
  \A t \in 1..W : Balanced(p, t)

Solutions ==
  { p \in Partitions(N, W) : BalancedAll(p) }

Init ==
  IF Solutions = {} THEN
    pieces = << >>
  ELSE
    pieces \in Solutions

Next ==
  UNCHANGED pieces

Spec ==
  Init /\ [][Next]_<<pieces>>

\* Safety invariants (hold vacuously if no solution exists)
PartitionInvariant ==
  (Solutions = {}) \/ (pieces \in Partitions(N, W))

BalancedInvariant ==
  (Solutions = {}) \/ BalancedAll(pieces)

LengthInvariant ==
  (Solutions = {}) \/ (Len(pieces) = N)

SumInvariant ==
  (Solutions = {}) \/ (SumSeq(pieces) = W)

\* TLC-oriented search and report: print a solution if one exists, else report none.
ASSUME
  LET sols == Solutions IN
    PrintT(
      IF sols # {} THEN
        << "Solution found", [W |-> W, N |-> N], CHOOSE s \in sols : TRUE >>
      ELSE
        << "No solution exists", [W |-> W, N |-> N] >>
    ) = TRUE

====