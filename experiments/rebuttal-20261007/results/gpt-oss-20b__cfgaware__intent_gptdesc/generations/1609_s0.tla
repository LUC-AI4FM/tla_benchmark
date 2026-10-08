------------------------------ MODULE Quicksort ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS ArrayLen \* positive integer
          DOMAIN   \* finite set of comparable values (e.g., integers)

VARIABLES Arr, Subranges

(* Type definitions *)
ArrType == [1..ArrayLen -> DOMAIN]
SubrangeSet == {<<l,r>> : 1 <= l /\ l <= r /\ r <= ArrayLen}

Variables ==
    Arr \in ArrType /\
    Subranges \subseteq SubrangeSet

(* Initial state: arbitrary array, whole range unsorted *)
Init ==
    /\ Arr \in ArrType
    /\ Subranges = {<<1,ArrayLen>>}

(* Helper predicate for partition step *)
PartitionPossible(Arr, Arr', l, r, p, q) ==
    /\ Arr'[q] = Arr[p]
    /\ \A i,j \in [l,r] :
          (i < q /\ j > q) => Arr'[i] <= Arr'[j]
    /\ \A k \notin [l,r] : Arr'[k] = Arr[k]

(* Next-state relation *)
Next ==
    \E l,r,p,q \in 1..ArrayLen :
        /\ <<l,r>> \in Subranges
        /\ l <= p /\ p <= r
        /\ PartitionPossible(Arr, Arr', l, r, p, q)
        /\ Subranges' =
              (Subranges \ {<<l,r>>}) 
              \cup (IF l <= q-1 THEN {<<l,q-1>>} ELSE {})
              \cup (IF q+1 <= r THEN {<<q+1,r>>} ELSE {})

(* Variant for termination *)
Variant ==
    \SUM_{s \in Subranges} (s[2] - s[1] + 1)

(* Invariant: variant decreases on each Next step *)
VariantDecrease == 
    [] (Next => Variant' < Variant)

(* Sorted predicate *)
Sorted ==
    \A i \in 1..ArrayLen-1 : Arr[i] <= Arr[i+1]

(* Ensure that when no subrange remains, the array is sorted *)
SortedAtEnd ==
    [] (Subranges = {} => Sorted)

Spec == Init /\ [][Next]_<<Arr, Subranges>> /\ VariantDecrease /\ SortedAtEnd

Termination ==
    <> (Subranges = {})

=============================================================================