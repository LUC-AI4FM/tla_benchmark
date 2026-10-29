---------------------------- MODULE Majority ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Value
ASSUME ConstAssump == Value # {}

VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

\* Bound on sequence length so that TLC can enumerate initial states
MaxLen == 4

BoundedSeq(S, n) == UNION { [1 .. k -> S] : k \in 0 .. n }

TypeOK ==
  /\ seq \in Seq(Value)
  /\ i \in 1 .. Len(seq) + 1
  /\ cand \in Value
  /\ cnt \in Nat

Init ==
  /\ seq \in BoundedSeq(Value, MaxLen)
  /\ i = 1
  /\ cand \in Value
  /\ cnt = 0

Next ==
  /\ i <= Len(seq)
  /\ i' = i + 1
  /\ seq' = seq
  /\ \/ /\ cnt = 0
        /\ cand' = seq[i]
        /\ cnt' = 1
     \/ /\ cnt # 0
        /\ cand = seq[i]
        /\ cand' = cand
        /\ cnt' = cnt + 1
     \/ /\ cnt # 0
        /\ cand # seq[i]
        /\ cand' = cand
        /\ cnt' = cnt - 1

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Positions and number of occurrences of value v in sequence s
positions(v, s) == { k \in 1 .. Len(s) : s[k] = v }
occurrences(v, s) == Cardinality(positions(v, s))

Correct ==
  i > Len(seq) =>
    \A v \in Value : 2 * occurrences(v, seq) > Len(seq) => v = cand

Inv ==
  LET prefix == SubSeq(seq, 1, i-1)
  IN  /\ cnt <= occurrences(cand, prefix)
      /\ 2 * (occurrences(cand, prefix) - cnt) <= i - 1 - cnt
      /\ \A v \in Value \ {cand} :
            2 * occurrences(v, prefix) <= i - 1 - cnt

=============================================================================