------------------------------- MODULE Chameneos -------------------------------

CONSTANTS M \* Number of creatures
          N \* Total number of meetings required

VARIABLES colors \* Colors of each creature
          mall   \* State of the mall (either a color or "empty")
          met    \* Personal meeting count for each creature
          totalMet \* Total number of pairwise meetings

ColorSet == {"blue", "red", "yellow"}

ComplementColor(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE CHOOSE c \in ColorSet : c /= c1 /\ c /= c2

Init ==
  /\ colors \in [1..M -> ColorSet]
  /\ mall = "empty"
  /\ met \in [1..M -> 0]
  /\ totalMet = 0

Arrive(i) ==
  /\ mall = "empty"
  /\ totalMet < N
  /\ \/ \E j \in 1..M : colors[j] /= colors[i]
     \/ \A j \in 1..M : colors[j] = colors[i]
  /\ mall' = colors[i]

Meet(i) ==
  /\ mall /= "empty"
  /\ totalMet < N
  /\ LET otherColor == mall
     IN /\ colors' = [colors EXCEPT ![i] = ComplementColor(colors[i], otherColor)]
        /\ met' = [met EXCEPT ![i] = met[i] + 1]
        /\ totalMet' = totalMet + 1
        /\ mall' = "empty"

Fade(i) ==
  /\ totalMet >= N
  /\ mall = colors[i]
  /\ mall' = "empty"

Next ==
  \/ \E i \in 1..M : Arrive(i)
  \/ \E i \in 1..M : Meet(i)
  \/ \E i \in 1..M : Fade(i)

Spec ==
  Init /\ [][Next]_<<colors, mall, met, totalMet>>

TypeOK ==
  /\ colors \in [1..M -> ColorSet]
  /\ mall \in ColorSet \/ mall = "empty"
  /\ met \in [1..M -> Nat]
  /\ totalMet \in Nat

SumMet ==
  LET sum == \E s \in SUBSET 1..M : \A i \in 1..M : (i \in s <-> met[i] > 0) /\ SUM {met[i]: i \in s}
  IN sum = 2 * totalMet

=============================================================================