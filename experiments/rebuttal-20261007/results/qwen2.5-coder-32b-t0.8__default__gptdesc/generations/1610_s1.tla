------------------------------- MODULE QuickSortSpec -------------------------------
EXTENDS TLC, Integers

CONSTANTS N
VARIABLES arr, S, pc

(* --algorithm QuickSort
variables arr = [1..N -> 0], S = {[1,N]}, pc = "qs1"

qs1:
    while (pc = "qs1") {
        if S /= {} then {
            with (lo, hi) \in S do
                assert lo <= hi;
                let pivot \in {lo..hi} do
                    let left = [lo..pivot-1 -> x \in 1..N : arr[x]],
                        right = [pivot+1..hi -> y \in 1..N : arr[y]] in
                    with permutedArr \in Permutations(arr) do
                        assert \A i \in lo..pivot-1 : permutedArr[i] \leq permutedArr[pivot];
                        assert \A i \in pivot+1..hi : permutedArr[pivot] <= permutedArr[i];
                        arr := permutedArr;
                        S := (S \ {[lo, hi]}) \cup {[lo, pivot-1]} \cup {[pivot+1, hi]};
        } else {
            pc := "Done";
        };
    };

end algorithm *)

Init == /\ arr \in [1..N -> 1..N]
        /\ S = {[1,N]}
        /\ pc = "qs1"

Next ==
    \/ /\ pc = "qs1"
       /\ \/ /\ S /= {}
              /\ \/ \E lo, hi \in 1..N : <<lo, hi>> \in S
                     /\ \E pivot \in lo..hi :
                        \E permutedArr \in Permutations(arr) :
                            (\A i \in lo..pivot-1 : permutedArr[i] \leq permutedArr[pivot])
                            /\ (\A i \in pivot+1..hi : permutedArr[pivot] <= permutedArr[i])
                            /\ arr' = permutedArr
                            /\ S' = (S \ {[lo, hi]}) \cup {[lo, pivot-1]} \cup {[pivot+1, hi]}
                            /\ pc' = "qs1"
              /\ \/ S = {}
                     /\ arr' = arr
                     /\ S' = S
                     /\ pc' = "Done"

Spec ==
    /\ Init
    /\ [][Next]_<<arr, S, pc>>
    /\ WF_[Next]_<<arr, S, pc>>

Termination == <>[](pc = "Done")
=============================================================================