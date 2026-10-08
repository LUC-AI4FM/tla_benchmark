MODULE SmallPlusCal
EXTENDS Naturals, Integers

VARIABLES x, pc

Init == /\ pc = "Start"
        /\ x ∈ 1..10

Step ==
  /\ pc = "Start"
  /\ x^2 <= 100
  /\ pc' = "Done"
  /\ x' = x

Stutter ==
  /\ pc = "Done"
  /\ pc' = pc
  /\ x' = x

Next == Step \/ Stutter

Spec == Init /\ [][Next]_<<x,pc>>

SafetyInvariant == x^2 <= 100

Termination == <> (pc = "Done")

FullSpec == Spec /\ SafetyInvariant /\ Termination