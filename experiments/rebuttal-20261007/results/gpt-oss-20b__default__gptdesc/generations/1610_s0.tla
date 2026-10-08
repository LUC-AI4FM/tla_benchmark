MODULE QuickSortPlusCal
CONSTANTS N

VARIABLES arr, S, pc

(* Type definitions *)
ArrType == [1..N -> 1..N]
Interval == <<low, high>> where low ∈ 1..N /\ high ∈ 1..N /\ low <= high

IsInterval(i) ==
  /\ i[1] ∈ 1..N
  /\ i[2] ∈ 1..N
  /\ i[1] <= i[2]

(* Permutation predicate *)
Permutation(a,b) ==
  ∀ v ∈ 1..N: \#({ i | a[i] = v }) = \#({ i | b[i] = v })

(* Initial state *)
Init ==
  /\ arr ∈ ArrType
  /\ S = {<<1,N>>}
  /\ pc = "qs1"

(* Partition action *)
Partition ==
  /\ pc = "qs1"
  /\ S ≠ {}
  /\ I ∈ S
  /\ low = I[1]
  /\ high = I[2]
  /\ low <= high
  /\ p ∈ 1..N
  /\ low <= p <= high
  /\ arr' ∈ ArrType
  /\ Permutation(arr, arr')
  /\ ∀ i ∈ low .. p-1: arr'[i] <= arr'[p]
  /\ ∀ j ∈ p+1 .. high: arr'[j] >= arr'[p]
  /\ S' = (S \ {I}) 
          ∪ IF low <= p-1 THEN {<<low, p-1>>} ELSE {}
          ∪ IF p+1 <= high THEN {<<p+1, high>>} ELSE {}
  /\ pc' = "qs1"

(* Done action *)
Done ==
  /\ pc = "qs1"
  /\ S = {}
  /\ pc' = "Done"
  /\ arr' = arr
  /\ S' = {}

Next == Partition \/ Done

Spec == Init /\ [][Next]_<<arr,S,pc>> /\ WF_0(Next)

Termination == <> (pc = "Done")