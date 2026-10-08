```
MODULE BalanceScale
EXTENDS Integers, Sequences, TLC

CONSTANTS W, N

VARIABLES pieces, targetWeight

Init ==
  /\ pieces = <<>>
  /\ targetWeight = 1

Next ==
  /\ IF targetWeight <= W THEN
    /\ pieces' = Append(pieces, CHOOSE w \in Nat \ {0} : w <= W)
    /\ targetWeight' = targetWeight + 1
  ELSE
    /\ pieces' = pieces
    /\ targetWeight' = targetWeight

Spec ==
  /\ Init
  /\ [][Next]_pieces
  /\ WF_vars(Next)

Invariant ==
  /\ pieces \in Seq(Nat)
  /\ Len(pieces) <= N
  /\ targetWeight >= 1
  /\ targetWeight <= W + 1

BalanceProperty(w) ==
  \/ \exists seq \in Seq(Int) : Len(seq) = Len(pieces)
    /\ And [i \in 1..Len(pieces) |-> IF seq[i] = -1 THEN pieces[i] ELSEIF seq[i] = 0 THEN 0 ELSE pieces[i]]
    /\ SumSeq(seq) = w
  \/ \exists seq \in Seq(Int) : Len(seq) = Len(pieces)
    /\ And [i \in 1..Len(pieces) |-> IF seq[i] = -1 THEN pieces[i] ELSEIF seq[i] = 0 THEN 0 ELSE pieces[i]]
    /\ SumSeq(seq) = -w

SumSeq(seq) ==
  IF seq = <<>> THEN 0
  ELSE Head(seq) + SumSeq(Tail(seq))

THEOREM Spec => []\A w \in 1..W : BalanceProperty(w)

ASSUME PrintT == targetWeight > W
```
Note: This TLA+ module is intended to be used with the TLC model checker, and it uses TLC-oriented constructs such as `ASSUME` and `PrintT`. The `THEOREM` statement specifies the desired property of the system.