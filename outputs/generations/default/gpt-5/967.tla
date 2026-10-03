----------------------------- MODULE BalanceScale -----------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANTS W, N

ASSUME /\ W \in Nat \ {0}
       /\ N \in Nat \ {0}

VARIABLES pieces

Nat1 == Nat \ {0}

RECURSIVE Partitions(_, _)
Partitions(w, n) ==
  IF n = 0 THEN
    IF w = 0 THEN { << >> } ELSE {}
  ELSE
    LET maxFirst == w - (n - 1) IN
      IF maxFirst < 1 THEN {}
      ELSE UNION { { <<k>> \o tail : tail \in Partitions(w - k, n - 1) } : k \in 1..maxFirst }

RECURSIVE Sum1To(_, _)
Sum1To(n, f) ==
  IF n = 0 THEN 0 ELSE Sum1To(n - 1, f) + f[n]

Dot(s, c) == Sum1To(Len(s), LAMBDA i: c[i] * s[i])

AllTargetsBalanced(s) ==
  /\ Len(s) = N
  /\ \A t \in 1..W:
        \E c \in [1..Len(s) -> {-1, 0, 1}]:
          Dot(s, c) = t

TypeOK == pieces \in Partitions(W, N)

Init == pieces \in Partitions(W, N)

Next == UNCHANGED pieces

Spec == Init /\ [][Next]_<<pieces>>

Solutions == { s \in Partitions(W, N) : AllTargetsBalanced(s) }

ASSUME LET sols == Solutions IN
         IF sols # {} THEN
           PrintT(<<"Found solution:", CHOOSE s \in sols: TRUE>>)
         ELSE
           PrintT("No solution exists")

=============================================================================