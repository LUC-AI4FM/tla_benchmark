---------------------------- MODULE quicksort ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT ArrayLen

ASSUME ArrayLen \in Nat /\ ArrayLen >= 0

VARIABLES arr, arr0, pc, stack, lo, hi

vars == <<arr, arr0, pc, stack, lo, hi>>

-----------------------------------------------------------------------------
(* Helper operators *)

Perms(S) == 
    LET perms[T \in SUBSET S] ==
        IF T = {} THEN {<<>>}
        ELSE UNION {
            {<<x>> \o p : p \in perms[T \ {x}]} : x \in T
        }
    IN perms[S]

PermutationsOf(seq) ==
    LET n == Len(seq)
        indices == 1..n
    IN {[i \in indices |-> seq[p[i]]] : p \in Perms(indices)}

IsPermutation(s1, s2) ==
    /\ Len(s1) = Len(s2)
    /\ \A v \in UNION {Range(s1), Range(s2)} : 
        Cardinality({i \in 1..Len(s1) : s1[i] = v}) = 
        Cardinality({i \in 1..Len(s2) : s2[i] = v})
  WHERE Range(s) == {s[i] : i \in 1..Len(s)}

IsSorted(s) ==
    \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

Range(s) == {s[i] : i \in 1..Len(s)}

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ arr \in [1..ArrayLen -> 1..ArrayLen]
    /\ arr0 = arr
    /\ pc = "Start"
    /\ stack = <<>>
    /\ lo = 1
    /\ hi = ArrayLen

-----------------------------------------------------------------------------
(* Actions *)

Start ==
    /\ pc = "Start"
    /\ IF ArrayLen > 0
       THEN /\ pc' = "Call"
            /\ lo' = 1
            /\ hi' = ArrayLen
       ELSE /\ pc' = "Done"
            /\ lo' = lo
            /\ hi' = hi
    /\ UNCHANGED <<arr, arr0, stack>>

Call ==
    /\ pc = "Call"
    /\ IF lo < hi
       THEN /\ pc' = "Partition"
       ELSE /\ pc' = "Return"
    /\ UNCHANGED <<arr, arr0, stack, lo, hi>>

Partition ==
    /\ pc = "Partition"
    /\ \E pivotIdx \in lo..hi :
        \E newArr \in [1..ArrayLen -> Range(arr)] :
            /\ \A i \in 1..ArrayLen : 
                (i < lo \/ i > hi) => newArr[i] = arr[i]
            /\ LET subarr == [i \in 1..(hi - lo + 1) |-> arr[lo + i - 1]]
                   newSubarr == [i \in 1..(hi - lo + 1) |-> newArr[lo + i - 1]]
               IN /\ Len(newSubarr) = Len(subarr)
                  /\ \A v \in Range(subarr) \cup Range(newSubarr) :
                       Cardinality({i \in 1..Len(subarr) : subarr[i] = v}) =
                       Cardinality({i \in 1..Len(newSubarr) : newSubarr[i] = v})
            /\ \A i \in lo..pivotIdx, j \in (pivotIdx+1)..hi :
                newArr[i] <= newArr[j]
            /\ arr' = newArr
            /\ stack' = Append(stack, [l |-> lo, h |-> hi, p |-> pivotIdx])
            /\ lo' = lo
            /\ hi' = pivotIdx
            /\ pc' = "LeftCall"
    /\ UNCHANGED <<arr0>>

LeftCall ==
    /\ pc = "LeftCall"
    /\ IF lo < hi
       THEN pc' = "Partition"
       ELSE pc' = "LeftReturn"
    /\ UNCHANGED <<arr, arr0, stack, lo, hi>>

LeftReturn ==
    /\ pc = "LeftReturn"
    /\ LET frame == Head(stack)
       IN /\ lo' = frame.p + 1
          /\ hi' = frame.h
          /\ pc' = "RightCall"
    /\ UNCHANGED <<arr, arr0, stack>>

RightCall ==
    /\ pc = "RightCall"
    /\ IF lo < hi
       THEN /\ pc' = "Partition"
       ELSE /\ pc' = "RightReturn"
    /\ UNCHANGED <<arr, arr0, stack, lo, hi>>

RightReturn ==
    /\ pc = "RightReturn"
    /\ stack' = Tail(stack)
    /\ IF stack' = <<>>
       THEN /\ pc' = "Done"
            /\ UNCHANGED <<lo, hi>>
       ELSE /\ pc' = "LeftReturn"
            /\ UNCHANGED <<lo, hi>>
    /\ UNCHANGED <<arr, arr0>>

Return ==
    /\ pc = "Return"
    /\ IF stack = <<>>
       THEN /\ pc' = "Done"
            /\ UNCHANGED <<lo, hi, stack>>
       ELSE /\ LET frame == Head(stack)
               IN IF lo <= frame.p
                  THEN /\ pc' = "LeftReturn"
                       /\ UNCHANGED <<lo, hi, stack>>
                  ELSE /\ stack' = Tail(stack)
                       /\ IF Tail(stack) = <<>>
                          THEN /\ pc' = "Done"
                               /\ UNCHANGED <<lo, hi>>
                          ELSE /\ pc' = "LeftReturn"
                               /\ UNCHANGED <<lo, hi>>
    /\ UNCHANGED <<arr, arr0>>

-----------------------------------------------------------------------------
(* Next-state relation *)

Next ==
    \/ Start
    \/ Call
    \/ Partition
    \/ LeftCall
    \/ LeftReturn
    \/ RightCall
    \/ RightReturn
    \/ Return

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Termination property *)

Termination == <>(pc = "Done")

-----------------------------------------------------------------------------
(* Correctness invariant for final state *)

Correct ==
    pc = "Done" => 
        /\ IsSorted(arr)
        /\ \A v \in Range(arr) \cup Range(arr0) :
            Cardinality({i \in 1..ArrayLen : arr[i] = v}) =
            Cardinality({i \in 1..ArrayLen : arr0[i] = v})

=============================================================================