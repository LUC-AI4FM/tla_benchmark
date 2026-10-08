---- MODULE WeighingPuzzle ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS W, N

VARIABLES sol

PosInt == Nat \ {0}

RECURSIVE SumSeq(_)
SumSeq(s) ==
  IF Len(s) = 0 THEN 0 ELSE Head(s) + SumSeq(Tail(s))

IsNonDecreasing(s) ==
  \A i \in 1..(Len(s)-1): s[i] <= s[i+1]

Candidates ==
  { s \in Seq(PosInt) :
      /\ Len(s) = N
      /\ IsNonDecreasing(s)
      /\ SumSeq(s) = W }

Coeffs == {-1, 0, 1}

RECURSIVE AllSeqs(_, _)
AllSeqs(S, n) ==
  IF n = 0
    THEN { << >> }
    ELSE { Append(s, x) : s \in AllSeqs(S, n-1), x \in S }

RECURSIVE Dot(_, _)
Dot(c, s) ==
  IF Len(s) = 0
    THEN 0
    ELSE Head(c) * Head(s) + Dot(Tail(c), Tail(s))

CoversAll(s) ==
  /\ Len(s) = N
  /\ \A t \in 1..W:
        \E c \in AllSeqs(Coeffs, N) : Dot(c, s) = t

Solutions == { s \in Candidates : CoversAll(s) }

ASSUME
  PrintT(
    IF Solutions # {}
      THEN [solution |-> CHOOSE s \in Solutions : TRUE]
      ELSE "No solution"
  )
  =
  IF Solutions # {}
    THEN [solution |-> CHOOSE s \in Solutions : TRUE]
    ELSE "No solution"

Init ==
  IF Solutions # {}
    THEN sol = CHOOSE s \in Solutions : TRUE
    ELSE sol = "No solution"

Next == UNCHANGED sol

Spec == Init /\ [][Next]_sol

Inv ==
  sol = "No solution" \/ (sol \in Candidates /\ CoversAll(sol))

====