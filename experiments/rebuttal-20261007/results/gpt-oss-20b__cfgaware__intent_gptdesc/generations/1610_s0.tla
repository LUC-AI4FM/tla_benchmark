------------------------------ MODULE QuickSort ------------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS N
CONSTANTS InitArr \* initial array values, a sequence of length N

(* Type definitions *)
TYPEDEF 
  Index == 1..N

(* Helper predicates *)
InInterval(k, lo, hi) == lo <= k /\ k <= hi

(* Variables *)
VARIABLES arr, pending

(* Initial state *)
Init ==
  /\ arr \in [1..N -> Int]
  /\ arr = InitArr
  /\ IF N > 0 THEN pending = {<1,N>} ELSE pending = {}

(* Process an interval with lo < hi *)
Process(lo, hi) ==
  /\ lo < hi
  /\ \E p \in Index : lo <= p /\ p < hi
     /\ \E f \in [lo..hi -> lo..hi] :
          Inverse(f) ∈ [lo..hi -> lo..hi]
          /\ (\A k \in 1..N :
                IF InInterval(k, lo, hi)
                   THEN arr'[k] = arr[f(k)]
                   ELSE arr'[k] = arr[k])
          /\ (\A i,j \in 1..N :
                IF InInterval(i, lo, p) /\ InInterval(j, p+1, hi)
                   THEN arr'[i] <= arr'[j]
                   ELSE TRUE)
     /\ pending' = (pending \ {<lo,hi>}) ∪ {<lo,p>, <p+1,hi>}

(* Skip an interval with lo >= hi *)
Skip(lo, hi) ==
  /\ lo >= hi
  /\ (\A k \in 1..N : arr'[k] = arr[k])
  /\ pending' = pending \ {<lo,hi>}

(* Step action: pick any pending interval and process or skip it *)
Step ==
  \E lo, hi \in Index :
    <lo,hi> ∈ pending
    /\ (Process(lo,hi) \/ Skip(lo,hi))

(* Specification *)
Spec == Init /\ [][Step]_<<arr,pending>>

(* Invariant: arr is always a permutation of the initial array *)
PermutationInvariant ==
  \E f \in [1..N -> 1..N] :
    Inverse(f) ∈ [1..N -> 1..N]
    /\ (\A i \in 1..N : arr[i] = InitArr[f(i)])

(* Sorted predicate *)
Sorted == \A i \in 1..(N-1) : arr[i] <= arr[i+1]

(* Ordering progress: when no pending intervals, array is sorted *)
OrderingProgress == []((pending = {}) => Sorted)

(* Termination property: eventually no pending intervals remain *)
Termination == []<>(pending = {})

(* Fairness assumption to guarantee liveness *)
FairnessAssumption == WF_{Step}

=============================================================================