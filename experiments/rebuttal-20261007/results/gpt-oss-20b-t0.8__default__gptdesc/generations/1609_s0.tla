MODULE QuickSort
EXTENDS Naturals, Sequences

CONSTANTS ArrayLen, InitArr

VARIABLES arr, stack, pc

(* Frame type *)
Frame == [ left : Nat, right : Nat ]

PushFrames(rest,l,p,r) ==
  LET rest1 == IF l <= p-1 THEN << [left |-> l, right |-> p-1] >> \o rest ELSE rest
      rest2 == IF p+1 <= r THEN << [left |-> p+1, right |-> r] >> \o rest1 ELSE rest1
  IN rest2

PermuteAndPartition(old,new,l,r,p) ==
  LET pivotVal == old[p]
  IN
    \E sigma \in [l..r -> l..r] :
      /\ (\A i,j ∈ [l..r] : sigma[i] = sigma[j] => i=j)
      /\ (\A j ∈ [l..r] : \E i ∈ [l..r] : sigma[i] = j)
      /\ \A i ∈ 1..ArrayLen :
          IF i ∈ [l..r] THEN new[i] = old[sigma[i]] ELSE new[i] = old[i]
      /\ new[p] = old[p]
      /\ \A i,j ∈ [l..r] : (i <= p /\ j > p) => new[i] <= new[j]

PermutesFull(A,B) ==
  \E sigma \in [1..ArrayLen -> 1..ArrayLen] :
    /\ (\A i,j ∈ [1..ArrayLen] : sigma[i] = sigma[j] => i=j)
    /\ (\A j ∈ [1..ArrayLen] : \E i ∈ [1..ArrayLen] : sigma[i] = j)
    /\ \A i ∈ 1..ArrayLen : B[i] = A[sigma[i]]

Sorted(arr) == \A i,j ∈ 1..ArrayLen : i < j => arr[i] <= arr[j]

Init ==
  /\ arr = InitArr
  /\ stack = << [left |-> 1, right |-> ArrayLen] >>
  /\ pc = "Start"

Partition ==
  LET t == Head(stack)
      l == t.left
      r == t.right
  IN
    /\ pc = "Start"
    /\ l <= r
    /\ p \in [l..r]
    /\ \E arr' \in [1..ArrayLen -> Nat] :
        /\ PermuteAndPartition(arr, arr', l, r, p)
        /\ stack' = PushFrames(Tail(stack), l, p, r)
        /\ pc' = "Start"

DoneTransition ==
  /\ stack = <<>>
  /\ pc = "Start"
  /\ pc' = "Done"
  /\ arr' = arr
  /\ stack' = stack

Next == Partition \/ DoneTransition

vars == <<arr, stack, pc>>

Spec ==
  Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
  /\ <> (pc = "Done")
  /\ [] (pc = "Done" => Sorted(arr))
  /\ [] (PermutesFull(arr, InitArr))

END QuickSort