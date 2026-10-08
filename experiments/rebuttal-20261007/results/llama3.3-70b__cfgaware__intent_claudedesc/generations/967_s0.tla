---------------------------- MODULE BalanceScale ----------------------------
EXTENDS Integers

CONSTANT W, N

VARIABLE partition, found

Init ==
  /\ partition = <<>>
  /\ found = FALSE

Next ==
  /\ partition' \in NonDecreasingSequences(W, N)
  /\ IF found
    THEN UNCHANGED <<partition, found>>
    ELSE /\ found' = CanMeasureAllWeights(partition')
         /\ IF found'
           THEN partition' = partition
           ELSE partition' = Append(partition, 1)

CanMeasureAllWeights(seq) ==
  \A w \in 1..W : \E coefficients \in [1..N -> {-1, 0, 1}] :
    w = +[i \in 1..N |-> IF coefficients[i] = 1 THEN seq[i] ELSE IF coefficients[i] = -1 THEN -seq[i] ELSE 0]

NonDecreasingSequences(w, n) ==
  {<<s1, s2, ..., sn>> \in [1..n -> 1..w] : 
    /\ +[i \in 1..n |-> s_i] = w
    /\ \A i, j \in 1..n : i <= j => s_i <= s_j}

Append(seq, num) ==
  <<s1, s2, ..., sn>> ++ <<num>>

Spec ==
  Init /\ [][Next]_<<partition, found>>

THEOREM Spec => []found
=============================================================================