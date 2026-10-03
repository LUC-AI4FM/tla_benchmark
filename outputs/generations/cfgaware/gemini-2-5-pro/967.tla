-------------------------- MODULE BalanceScale --------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS
  \* The total weight to be partitioned and measured.
  W,
  \* The number of pieces to cut the total weight into.
  N

\* A recursive operator to sum the elements of a sequence of numbers.
RECURSIVE Sum(_)
Sum(s) ==
  IF s = <<>> THEN 0
  ELSE Head(s) + Sum(Tail(s))

\* A recursive operator to generate all ordered partitions of a total
\* into a specified number of positive integer pieces.
\* An ordered partition of `t` into `n` pieces is a sequence `s` such that:
\* 1. Len(s) = n
\* 2. Sum(s) = t
\* 3. \A i \in DOMAIN s: s[i] \in Nat \ {0}
RECURSIVE OrderedPartitions(_, _)
OrderedPartitions(total, num_pieces) ==
  IF num_pieces = 0 THEN
    IF total = 0 THEN {<<>>} ELSE {}
  ELSE IF total < num_pieces THEN
    {}  \* Impossible to partition 'total' into 'num_pieces' positive integers.
  ELSE IF num_pieces = 1 THEN
    {<<total>>}
  ELSE
    LET heads == 1..(total - (num_pieces - 1))
    IN { <<h>> \o t :
           h \in heads,
           t \in OrderedPartitions(total - h, num_pieces - 1) }

\* An operator that checks if a given sequence of pieces is a valid solution.
\* A solution must be able to balance every integer weight from 1 to W.
IsSolution(pieces) ==
  LET \* A recursive helper to compute the set of all weights that can be
      \* achieved by placing the given pieces on either side of a balance scale.
      \* This is equivalent to sums of the form c_1*p_1 + ... + c_k*p_k
      \* where c_i \in {-1, 0, 1}.
      RECURSIVE AchievableWeights(_)
      AchievableWeights(p) ==
        IF p = <<>> THEN
          {0}
        ELSE
          LET prev = AchievableWeights(Tail(p))
              h = Head(p)
          IN prev \cup { w + h : w \in prev } \cup { w - h : w \in prev }

      Reachable == AchievableWeights(pieces)
  IN \A target \in 1..W : target \in Reachable

\* The set of all candidate partitions.
AllPartitions == OrderedPartitions(W, N)

\* A valid solution, if one exists. TLC will search for a value that
\* satisfies this definition.
Solution == CHOOSE pieces \in AllPartitions : IsSolution(pieces)

\* The following ASSUME statements guide TLC's behavior.
\*
\* The first ASSUME tells TLC that a solution is guaranteed to exist.
\* This prevents TLC from complaining that the set passed to CHOOSE might be empty.
\* If no solution exists for the given W and N, this assumption will be violated,
\* and TLC will report an error, effectively telling us there is no solution.
ASSUME \E pieces \in AllPartitions : IsSolution(pieces)

\* The second ASSUME uses PrintT to force TLC to evaluate the 'Solution'
\* operator and print its value. This is how we get the answer.
ASSUME PrintT(Solution)

=============================================================================