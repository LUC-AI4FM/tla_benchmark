```
MODULE StoneCutting
EXTENDS Naturals, Sequences

CONSTANTS W, N

ASSUME
  (W \in Nat) /\ (N \in Nat) /\ (W > 0) /\ (N > 0)

(* Enumerate all ordered partitions of w into n natural numbers *)
Partitions(n, w) ==
  IF n = 0 THEN
    IF w = 0 THEN {<>} ELSE {}
  ELSE
    { seq |
      ∃ first \in 1..w :
        LET rest == Partitions(n-1, w-first) IN
          seq = <first>~rest }

(* Sum of a sequence *)
SeqSum(s) ==
  IF Len(s) = 0 THEN 0
  ELSE Head(s) + SeqSum(Tail(s))

(* All sequences of length n with elements in {-1,0,1} *)
CoeffSequences(n) ==
  { c | c \in Seq({-1,0,1}) /\ Len(c)=n }

(* Weighted sum of a coefficient sequence and a weight sequence *)
WeightedSum(coeff, seq) ==
  SUM [i \in 1..Len(seq)] -> coeff[i]*seq[i]

(* A partition is weighable if every target weight can be achieved *)
Weighable(seq) ==
  ∀ w \in 1..W :
    ∃ c \in CoeffSequences(N) : WeightedSum(c, seq) = w

Solutions == { s \in Partitions(N,W) | Weighable(s) }

(* Variables (dummy stuttering variable to satisfy the spec template) *)
VARIABLES dummy

Init == dummy = 0
Next == dummy' = dummy

Spec == Init /\ [] Next

ASSUME
  IF Solutions = {} THEN
    PrintT("No solution", TRUE)
  ELSE
    PrintT("solutions", Solutions)

END MODULE
```