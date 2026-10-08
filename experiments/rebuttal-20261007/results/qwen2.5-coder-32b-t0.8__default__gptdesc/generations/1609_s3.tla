------------------------------- MODULE QuicksortSpec -------------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS ArrayLen

VARIABLES arr, pc, stack, subarrayStarts, subarrayEnds

Init == 
  /\ arr \in [1..ArrayLen -> Nat]
  /\ pc = "Start"
  /\ stack = << >>
  /\ subarrayStarts = 1
  /\ subarrayEnds = ArrayLen

ChoosePivot(subStart, subEnd) ==
  LET pivotIndex \in {subStart .. subEnd} 
  IN arr' = [arr EXCEPT ![pivotIndex] = arr[pivotIndex]]
     /\ subarrayStarts' = subStart
     /\ subarrayEnds' = subEnd

Partition(subStart, subEnd, pivot) ==
  LET ltSeq == <<x \in seq : x <= pivot>> 
      gtSeq == <<x \in seq : x > pivot>>
      seq == [subStart..subEnd -> arr]
  IN \E perm \in Permutations(seq):
       /\ FORALL i \in subStart..(subEnd - Len(gtSeq)): arr'[i] = perm[i - subStart + 1]
       /\ FORALL i \in ((subEnd - Len(gtSeq)) + 1)..subEnd: arr'[i] = perm[i - subStart + 1]

Next ==
  \/ /\ pc = "Start"
     /\ stack' = <<1, ArrayLen>>
     /\ pc' = "QS"
  \/ /\ pc = "QS"
     /\ LET subStart == Head(stack)
            subEnd == Tail(Head(Tail(stack)))
        IN \E pivot \in arr[subStart..subEnd]:
             ChoosePivot(subStart, subEnd)
             /\ Partition(subStart, subEnd, pivot)
             /\ IF subStart <= (pivot - 1) THEN
                  stack' = <<subStart, pivot-1>> \o stack
                ELSE
                  stack' = stack
             /\ IF (pivot + 1) <= subEnd THEN
                  stack' = <<pivot+1, subEnd>> \o stack'
                ELSE
                  stack' = stack'
             /\ pc' = "QS"
  \/ /\ pc = "QS"
     /\ stack # << >>
     /\ stack' = Tail(stack)
     /\ pc' = IF stack' = << >> THEN "Done" ELSE "QS"

Spec ==
  Init /\ [][Next]_<<arr, pc, stack>> /\ WF_next(<<arr, pc, stack>>)

(*--algorithm Quicksort
variables arr, stack;

begin
Start:
    with (stack := <<1, ArrayLen>>, pc := "QS");
QS:
    if pc = "QS" then
        if stack # << >> then
            let subStart = Head(stack);
                subEnd   = Tail(Head(Tail(stack)));
                pivot \in arr[subStart..subEnd]
            in with (ChoosePivot(subStart, subEnd),
                     Partition(subStart, subEnd, pivot),
                     if subStart <= (pivot - 1) then
                         stack := <<subStart, pivot-1>> \o stack;
                     else
                         skip;
                     if (pivot + 1) <= subEnd then
                         stack := <<pivot+1, subEnd>> \o stack;
                     else
                         skip;
                     pc := "QS")
        else with (pc := "Done");
end algorithm *)

=============================================================================