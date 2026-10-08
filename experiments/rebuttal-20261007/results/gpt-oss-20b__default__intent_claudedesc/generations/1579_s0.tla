MODULE TokenRing

EXTENDS Naturals, Sequences

CONSTANTS N, K

VARIABLES values

Init == /\ values \in [0 .. N-1 -> 0 .. K-1]
        /\ K > N
        /\ N > 0

Inc(x) == (x + 1) % K

Token(i) ==
  IF i = 0 THEN
    (values[0] = values[N-1])
  ELSE
    (i > 0 /\ values[i] != values[i-1])

HoldsToken == ∃i ∈ 0 .. N-1 : Token(i)

Act(i) ==
  IF i = 0 THEN
    /\ values[0] = values[N-1]
    /\ values' = [values EXCEPT ![0] = Inc(values[0])]
  ELSE
    /\ values[i] != values[i-1]
    /\ values' = [values EXCEPT ![i] = values[i-1]]

Next == ∨ i ∈ 0 .. N-1 : Act(i)

FairnessCond == ∀ i ∈ 0 .. N-1 : Fairness(Act(i))

Spec == Init /\ [][Next]_values /\ FairnessCond

SafetyInv == HoldsToken

LivenessProp == ◇ □ (∃!i ∈ 0 .. N-1 : Token(i))