---------------------------- MODULE CarTalkPuzzle ----------------------------
EXTENDS Integers

CONSTANT W, N

Partitions(seq, wt) ==
  IF seq = <<>> THEN
    wt = 0
  ELSE
    LET head == seq[1]
        tail == seq[2..]
        maxHead == wt - (N - Len(seq)) * 1
    IN
      \E h \in 1..maxHead :
        Partitions(<<h>> ^ tail, wt - h)

Weighs(seq, wt) ==
  \E coeffs \in [1..Len(seq) -> {-1, 0, 1}] :
    wt = +<<
      \Sum i \in 1..Len(seq) : seq[i] * coeffs[i]
    >>

ASSUME
  \E seq \in [1..N -> 1..W] :
    Partitions(<<>>, W) /\ 
    Weighs(seq, W) /\
    \A w \in 1..W : Weighs(seq, w)

PrintT == 
  IF \E seq \in [1..N -> 1..W] : 
      Partitions(<<>>, W) /\ 
      \A w \in 1..W : Weighs(seq, w)
  THEN
    "Solution found"
  ELSE
    "No solution"

=============================================================================