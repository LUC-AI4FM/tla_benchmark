------------------------------ MODULE QuickSort ------------------------------
EXTENDS Naturals, Sequences

CONSTANT ArrayLen \in Nat

VARIABLES A, pc, stack, InitA

(* Helper definitions *)

Indices(low, high) == {i | low <= i /\ i <= high}

ValuesIn(A, low, high) == {A[i] | i ∈ Indices(low,high)}

Count(A, low, high, val) ==
  # {i | i ∈ Indices(low,high) /\ A[i] = val}

PermutePartition(A, low, high, p) ==
  {B \in [1..ArrayLen -> Nat] :
    (∀i ∈ 1..ArrayLen : i < low \/ i > high => B[i] = A[i]) /\
    (∀i,j ∈ 1..ArrayLen :
        low <= i /\ i <= p /\ p+1 <= j /\ j <= high => B[i] <= B[j]) /\
    (∀v ∈ ValuesIn(A, low, high) : Count(B, low, high, v) = Count(A, low, high, v))
  }

Sorted(A) == ∀i,j ∈ 1..ArrayLen : i < j => A[i] <= A[j]

PermutationInvariant ==
  (∀v ∈ ValuesIn(InitA, 1, ArrayLen) :
      Count(A, 1, ArrayLen, v) = Count(InitA, 1, ArrayLen, v))

(* Initial state *)

Init == 
  /\ InitA \in [1..ArrayLen -> Nat]
  /\ A = InitA
  /\ pc = "QS"
  /\ stack = << (1, ArrayLen) >>

(* Next action *)

Next ==
  \/ (* Process current frame *)
    LET low == Head(stack)[1]
        high == Head(stack)[2] IN
      /\ pc = "QS"
      /\ stack # <<>>
      /\ IF low >= high THEN
           /\ A' = A
           /\ stack' = Tail(stack)
         ELSE
           /\ p \in Indices(low,high)
           /\ B \in PermutePartition(A, low, high, p)
           /\ A' = B
           /\ stack' = << (low, p-1), (p+1, high) >> ++ Tail(stack)
      /\ pc' = "QS"
  \/ (* Finish *)
    /\ pc = "QS"
    /\ stack = <<>>
    /\ pc' = "Done"
    /\ A' = A

(* Specification *)

Spec == Init /\ WF_0(Next)

Termination == <> (pc = "Done")

(* Optional invariant for testing *)

Inv == PermutationInvariant /\ Sorted(A)

=============================================================================