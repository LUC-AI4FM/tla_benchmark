------------------------------ MODULE MergeSort ------------------------------
EXTENDS Integers, Sequences, TLC
CONSTANTS ArrayLen, MaxVal

VARIABLES arr, stack, buf

(* Frame type *)
Frame == [low: 1..ArrayLen, high: 1..ArrayLen, stage: 0..3]

(* Helper functions *)
IsPerm(low, high, f, a) ==
    \A v \in 1..MaxVal :
        CARD({i \in low..high : f[i] = v}) =
        CARD({i \in low..high : a[i] = v})

SortedSeq(f, low, high) ==
    \A i,j \in low..high : i < j => f[i] <= f[j]

(* Initial state *)
Init == 
    /\ arr \in [1..ArrayLen -> 1..MaxVal]
    /\ buf \in [1..ArrayLen -> 1..MaxVal]
    /\ stack = << [low |-> 1, high |-> ArrayLen, stage |-> 0] >>

(* Next relation *)
Next ==
    \E top \in stack :
        LET low   == top.low
            high  == top.high
        IN
          CASE low >= high ->
                /\ stack' = Tail(stack)
          [] low < high /\ top.stage = 0 ->
                LET mid == (low + high) \div 2 IN
                    /\ stack' = Tail(stack) ++ << [low |-> low, high |-> high, stage |-> 3] >>
                    /\ stack' = stack' ++ << [low |-> mid+1, high |-> high, stage |-> 0] >>
                    /\ stack' = stack' ++ << [low |-> low, high |-> mid, stage |-> 0] >>
          [] top.stage = 3 ->
                \E f \in [low..high -> 1..MaxVal] :
                    IsPerm(low, high, f, arr) /\ SortedSeq(f, low, high)
                    /\ arr' = [arr EXCEPT ![low..high] = f]
                    /\ stack' = Tail(stack)

(* Safety invariant *)
SortedArr == \A i,j \in 1..ArrayLen : i < j => arr[i] <= arr[j]

SafetyInvariant == (stack = <<>>) => SortedArr

(* Liveness property *)
LivenessProperty == <> (stack = <<>>)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
=============================================================================