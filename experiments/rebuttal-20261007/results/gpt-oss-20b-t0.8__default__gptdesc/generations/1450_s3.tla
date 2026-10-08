MODULE RandomSubsetSample
VARIABLE x

S == {1,2,3,4,5,6,7,8,9}
T == 1..10

Init ==
  /\ x \in [S -> T]
  /\ ∃ R \subseteq [S -> T] : (#R = 1000) /\ x ∈ R

Next ==
  /\ x' = x

Inv == TRUE

Spec == Init /\ [][Next]_x