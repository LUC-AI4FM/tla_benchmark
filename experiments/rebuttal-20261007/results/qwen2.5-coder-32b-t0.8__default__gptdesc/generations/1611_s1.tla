------------------------------- MODULE RecursiveMergesort ------------------------------

EXTENDS Naturals, Sequences

CONSTANTS ArrayLen

VARIABLES pc, arr, b, stack, lo, hi, mid

DefineSort \defs
  /\ (lo = <<lo1>> => /\ lo1 \in 1..ArrayLen
                       /\ hi = <<hi1>> => /\ hi1 \in 1..ArrayLen
                                          /\ lo1 <= hi1)
  /\ (pc = "Done" => arr \in [1..ArrayLen -> Nat])
  /\ b \in [1..2*ArrayLen -> Nat]
  /\ stack \in SUBSET [1..ArrayLen -> <<Nat, Nat>>]

Init == 
  /\ pc = "Start"
  /\ \A i \in 1..ArrayLen : arr[i] \in 1..ArrayLen
  /\ \A j \in 1..2*ArrayLen : b[j] = 0
  /\ stack = {}

Next ==
  \/ /\ pc = "Start"
     /\ lo' = <<1>>
     /\ hi' = <<ArrayLen>>
     /\ pc' = "Sort"
     /\ UNCHANGED <<arr, b, stack>>

  \/ /\ DefineSort
     /\ pc = "Sort"
     /\ LET loval == CHOOSE x \in lo : TRUE
          hival == CHOOSE y \in hi : TRUE IN
        IF loval < hival THEN
          /\ mid' = <<(loval + hival) \div 2>>
          /\ stack' = [stack EXCEPT ![LEN(stack)+1] = <<loval, hival>>]
          /\ pc' = "Sort"
        ELSE
          /\ pc' = "Merge"
     /\ UNCHANGED <<arr, b>>

  \/ /\ DefineSort
     /\ pc = "Merge"
     /\ LET loval == CHOOSE x \in lo : TRUE
          hival == CHOOSE y \in hi : TRUE IN
        IF LEN(stack) > 0 THEN
          /\ mid' = <<(loval + hival) \div 2>>
          /\ stack' = [stack EXCEPT ![LEN(stack)] = <<>>]
          /\ pc' = "Merge"
        ELSE
          /\ pc' = "Done"
     /\ UNCHANGED <<arr, b>>

  \/ /\ DefineSort
     /\ pc = "Done"
     /\ UNCHANGED <<lo, hi, mid, arr, b, stack>>

Spec ==
  /\ Init
  /\ [][Next]_<<pc, lo, hi, mid, arr, b, stack>>
  /\ WF_[Next]_<<pc, lo, hi, mid, arr, b, stack>>

Termination == <>[](pc = "Done")

Sorted ==
  LET sortedSeq == <<arr[1], arr[2] .. arr[ArrayLen]>> IN
    \A i \in 1..(ArrayLen-1) : sortedSeq[i] <= sortedSeq[i+1]

THEOREM Spec => []<>Termination /\ [](pc = "Done" => Sorted)

=============================================================================