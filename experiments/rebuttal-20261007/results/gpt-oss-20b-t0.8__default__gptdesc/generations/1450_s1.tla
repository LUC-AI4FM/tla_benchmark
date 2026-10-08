MODULE RandomSubsetSpec

EXTENDS Sets

CONSTANTS S, T, Nsubset

VARIABLE x

(* There exists a random subset of size Nsubset of all functions from S to T
   that contains the current value x *)
RandomSubsetExists ==
  \E Sub \in SUBSET([S -> T]) : (#Sub = Nsubset /\ x \in Sub)

Init == 
  /\ x \in [S -> T]
  /\ RandomSubsetExists

Next == x' = x

Inv == TRUE

Spec == Init /\ [][Next]_x

====