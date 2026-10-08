MODULE RandomSubsetSample
CONSTANT RandomSubsetSet

VARIABLE x

Init ==
   /\ x \in RandomSubsetSet
   /\ RandomSubsetSet \subseteq [1..9 -> 1..10]

Next == 
   x' = x

Spec == Init /\ [][Next]_x

Inv == TRUE

===============================================================================