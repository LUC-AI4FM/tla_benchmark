------------------------------ MODULE quicksort ------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS ArrayLen

ASSUME ArrayLen \in Nat /\ ArrayLen > 0

VARIABLES A, A0, pc, stack, lo, hi

vars == <<A, A0, pc, stack, lo, hi>>

(* Helper definitions *)

Range(f) == {f[i] : i \in DOMAIN f}

Indices == 1..ArrayLen

(* A permutation of sequence s is a sequence t such that 
   there exists a bijection from DOMAIN s to DOMAIN t 
   where t[bij[i]] = s[i] for all i *)
   
PermsOf(s) == 
    {t \in [DOMAIN s -> Range(s)] : 
        /\ DOMAIN t = DOMAIN s
        /\ \A v \in Range(s) : 
            Cardinality({i \in DOMAIN s : s[i] = v}) = 
            Cardinality({i \in DOMAIN t : t[i] = v})}

(* Check if array is sorted in nondecreasing order *)
IsSorted(arr) == \A i, j \in DOMAIN arr : i < j => arr[i] <= arr[j]

(* Check if two arrays are permutations of each other *)
IsPermutation(arr1, arr2) ==
    /\ DOMAIN arr1 = DOMAIN arr2
    /\ \A v \in Range(arr1) : 
        Cardinality({i \in DOMAIN arr1 : arr1[i] = v}) = 
        Cardinality({i \in DOMAIN arr2 : arr2[i] = v})

(* Initial state *)
Init == 
    /\ A \in [Indices -> 1..ArrayLen]  \* Array with values from 1 to ArrayLen
    /\ A0 = A                           \* Save initial array for invariant checking
    /\ pc = "Call"                      \* Initial control state
    /\ stack = <<>>                     \* Empty call stack
    /\ lo = 1                           \* Initial low bound
    /\ hi = ArrayLen                    \* Initial high bound

(* Procedure call to QS(lo, hi) *)
CallQS ==
    /\ pc = "Call"
    /\ IF lo >= hi
       THEN 
           \* Base case: subarray of size 0 or 1, return
           IF stack = <<>>
           THEN pc' = "Done" /\ lo' = lo /\ hi' = hi /\ stack' = stack /\ A' = A
           ELSE 
               \* Pop from stack and return
               /\ pc' = "Return"
               /\ lo' = lo
               /\ hi' = hi
               /\ stack' = stack
               /\ A' = A
       ELSE
           \* Recursive case: choose pivot and partition
           /\ pc' = "Partition"
           /\ lo' = lo
           /\ hi' = hi
           /\ stack' = stack
           /\ A' = A
    /\ A0' = A0

(* Partition step: nondeterministically choose pivot and partition *)
Partition ==
    /\ pc = "Partition"
    /\ \E pivot \in lo..hi :
        \E newA \in [Indices -> Range(A)] :
            \* Preserve elements outside [lo..hi]
            /\ \A i \in Indices : (i < lo \/ i > hi) => newA[i] = A[i]
            \* The subarray [lo..hi] is a permutation of original [lo..hi]
            /\ \A v \in Range(A) : 
                Cardinality({i \in lo..hi : A[i] = v}) = 
                Cardinality({i \in lo..hi : newA[i] = v})
            \* Partitioned: all elements at or before pivot position <= all elements after
            /\ \A i \in lo..pivot, j \in (pivot+1)..hi : newA[i] <= newA[j]
            \* Update state
            /\ A' = newA
            /\ stack' = Append(stack, [retLo |-> lo, retHi |-> hi, pivotPos |-> pivot])
            /\ lo' = lo
            /\ hi' = pivot  \* Will sort left part first
            /\ pc' = "Call"
    /\ A0' = A0

(* Return from recursive call *)
Return ==
    /\ pc = "Return"
    /\ stack # <<>>
    /\ LET frame == Head(stack)
       IN IF hi = frame.pivotPos
          THEN 
              \* Returning from left recursive call, now do right
              /\ lo' = frame.pivotPos + 1
              /\ hi' = frame.retHi
              /\ stack' = Tail(stack)
              /\ pc' = "CallRight"
              /\ A' = A
          ELSE
              \* Returning from right recursive call
              IF Len(Tail(stack)) = 0
              THEN 
                  /\ pc' = "Done"
                  /\ stack' = Tail(stack)
                  /\ lo' = lo
                  /\ hi' = hi
                  /\ A' = A
              ELSE
                  /\ pc' = "Return"
                  /\ stack' = Tail(stack)
                  /\ lo' = lo
                  /\ hi' = hi
                  /\ A' = A
    /\ A0' = A0

(* Call right subarray *)
CallRight ==
    /\ pc = "CallRight"
    /\ IF lo >= hi
       THEN
           \* Base case for right side
           IF stack = <<>>
           THEN pc' = "Done" /\ lo' = lo /\ hi' = hi /\ stack' = stack /\ A' = A
           ELSE 
               /\ pc' = "Return" 
               /\ lo' = lo 
               /\ hi' = hi 
               /\ stack' = stack 
               /\ A' = A
       ELSE
           \* Need to partition right side
           /\ pc' = "Partition"
           /\ lo' = lo
           /\ hi' = hi
           /\ stack' = stack
           /\ A' = A
    /\ A0' = A0

(* Terminal state *)
Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

(* Next state relation *)
Next == 
    \/ CallQS
    \/ Partition
    \/ Return  
    \/ CallRight
    \/ Done

(* Specification with weak fairness *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Safety invariant: A is always a permutation of A0 *)
PermutationInvariant == IsPermutation(A, A0)

(* Type invariant *)
TypeInvariant ==
    /\ A \in [Indices -> Int]
    /\ A0 \in [Indices -> Int]
    /\ pc \in {"Call", "Partition", "Return", "CallRight", "Done"}
    /\ lo \in 1..(ArrayLen+1)
    /\ hi \in 0..ArrayLen

(* Termination property *)
Termination == <>(pc = "Done")

(* Final state correctness: when done, array is sorted and is permutation of original *)
FinalStateCorrect == 
    pc = "Done" => (IsSorted(A) /\ IsPermutation(A, A0))

=============================================================================