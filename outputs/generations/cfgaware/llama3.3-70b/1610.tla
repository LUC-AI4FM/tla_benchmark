---------------------------- MODULE Quicksort ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE S, pc, a

qs1 == 
  /\ pc = "qs1"
  /\ * Choose an interval (l, r) from the set of subarray intervals still to be processed
  /\ EXISTS l \in S : 
    /\ * Select a pivot position within the chosen interval
      EXISTS p \in [l..N] :
        /\ * Replace the current array by a permutation of itself that satisfies the partition ordering constraints around the pivot
          a' = [i \in 1..N |-> IF i < l OR i > N THEN a[i] ELSE 
            IF a[i] < a[p] THEN a[<<j \in l..p : a[j] < a[p] >>[1]] 
            ELSE IF a[i] = a[p] THEN a[p] 
                   ELSE a[<<j \in p+1..r : a[j] > a[p]>>[1]]]]
        /\ * Update the set of subarray intervals still to be processed
          S' = (S \ {l}) \cup {[l, p-1], [p+1, r]}
  /\ pc' = "qs2"

Next == 
  /\ pc = "qs1" => qs1
  /\ pc = "qs2" => 
    /\ * If there are no more subarray intervals to be processed, the algorithm terminates
      IF S = {} THEN pc' = "Done"
      ELSE pc' = "qs1"

Spec == 
  /\ * The initial state: an array of length N with entries ranging over 1..N and a set containing the entire array as the only subarray interval to be processed
    (pc = "qs1") /\ (S = {[1, N]}) /\ (a \in [1..N -> 1..N])
  /\ [][Next]_<<pc, S, a>>
  /\ WF_<<pc, S, a>>(Next)

Termination == <>[](pc = "Done")
=============================================================================