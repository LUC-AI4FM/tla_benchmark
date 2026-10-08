------------------------------ MODULE QuickSort ------------------------------
EXTENDS Naturals, Integers

CONSTANT N \in Nat

VARIABLES arr, origArr, stack

(* Helper functions *)
Low(r) == r.low
High(r) == r.high

AddRange(stack, low, high) ==
   IF low <= high THEN stack \cup {[low |-> low, high |-> high]} ELSE stack

CountIn(arr, low, high, v) ==
   \# { i \in 1..N : low <= i /\ i <= high /\ arr[i] = v }

PermSub(arr, low, high, newArr) ==
   \A v \in DOMAIN(arr) :
      CountIn(arr, low, high, v) = CountIn(newArr, low, high, v)

CountAll(arr, v) == \# { i \in 1..N : arr[i] = v }

Permutation == \A v \in DOMAIN(origArr) : CountAll(arr, v) = CountAll(origArr, v)

Sorted == \A i,j \in 1..N : i < j => arr[i] <= arr[j]

(* Initial state *)
Init ==
   /\ arr \in [1..N -> Int]
   /\ origArr = arr
   /\ stack = {[low |-> 1, high |-> N]}

(* Next action: process one subarray *)
Process ==
   /\ r \in stack
   /\ low = Low(r)
   /\ high = High(r)
   /\ pivot \in low..high
   /\ \E newArr' \in [1..N -> Int] :
        /\ PermSub(arr, low, high, newArr')
        /\ (\A i \in low..pivot-1, j \in pivot+1..high : newArr'[i] <= newArr'[j])
        /\ arr' = [arr EXCEPT ![low..high] = newArr'[low..high]]
   /\ stack' = AddRange(AddRange(stack \ {r}, low, pivot-1), pivot+1, high)

Next == Process

Spec == Init /\ [][Next]_{<<arr, origArr, stack>>} /\ WF_vars(Next)

THEOREM Termination == <> (stack = {})

THEOREM SortedOnTermination == [] (stack = {} => Sorted /\ Permutation)

THEOREM PermInvariant == [] Permutation
END QuickSort