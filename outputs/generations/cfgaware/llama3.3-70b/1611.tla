---------------------------- MODULE Mergesort --------------------------------
EXTENDS Integers, Sequences

CONSTANT ArrayLen

VARIABLE a, b, pc, callStack

defaultInitValue == <<>>, <<>>, "Start", <<>>

Invariant == pc = "Done" => Sorted(a)

Sorted(seq) == 
  Len(seq) = 0 ∨ 
  (∀ i ∈ 1..(Len(seq) - 1) : seq[i] ≤ seq[i + 1])

TypeInv == a ∈ [1..ArrayLen → 1..ArrayLen] ∧
           b ∈ [1..ArrayLen → 1..ArrayLen] ∧
           pc ∈ {"Start", "Done"} ∧
           callStack ∈ Seq({"Split", "Merge"})

Init ==
  (pc = "Start") ∧ 
  (a = [i ∈ 1..ArrayLen |-> i]) ∧ 
  (b = [i ∈ 1..ArrayLen |-> 0]) ∧ 
  (callStack = <<>>)

Next ==
  pc = "Start" ∧ 
  callStack' = Append(<<>>, "Split") ∧ 
  a' = a ∧ b' = b ∧ pc' = "Split" ∨

  pc = "Split" ∧ 
  (Len(callStack) > 0) ∧ 
  (callStack[1] = "Split") ∧ 
  (∃ mid ∈ 1..(ArrayLen - 1) : 
    a' = [i ∈ 1..mid |-> a[i]] @ [i ∈ (mid + 1)..ArrayLen |-> 0] ∧
    b' = b ∧ 
    callStack' = Append(Tail(callStack), "Merge") ∧ 
    pc' = "Split" ∨

  pc = "Split" ∧ 
  (Len(callStack) > 0) ∧ 
  (callStack[1] = "Merge") ∧ 
  (∃ mid ∈ 1..(ArrayLen - 1) : 
    b' = Merge(a, mid) ∧
    a' = a ∧ 
    callStack' = Tail(callStack) ∧ 
    pc' = "Done" ∨

  pc = "Split" ∧ 
  (Len(callStack) = 0) ∧ 
  (callStack' = <<>>) ∧ 
  (a' = a) ∧ (b' = b) ∧ (pc' = "Done")

Merge(left, mid) == 
  [i ∈ 1..ArrayLen |-> IF i ≤ mid THEN left[i] ELSE left[mid + i - mid]]

Termination == <>[](pc = "Done")

Spec == Init ∧ □[Next]_a ∧ WF(Next)_(pc, callStack)

THEOREM Spec => Termination
=============================================================================