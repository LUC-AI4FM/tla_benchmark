------------------------------ MODULE RecursiveMergesort ------------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS ArrayLen

VARIABLES pc, i, j, k, low, high, mid, a, b, stack

Init == /\ pc = "Start"
        /\ a \in [1..ArrayLen -> Int]
        /\ b \in [1..ArrayLen -> Int]
        /\ stack = <<>>
        /\ low = 0
        /\ high = 0
        /\ mid = 0
        /\ i = 0
        /\ j = 0
        /\ k = 0

Next ==
    CASE pc = "Start" ->
         /\ low = 1
         /\ high = ArrayLen
         /\ stack = <<<<low, high>> >>
         /\ pc = "Sort"
    [] pc = "Sort" ->
         \/ /\ stack # <<>>
            /\ LET top == HD(stack)
               IN /\ low = fst(top)
                  /\ high = snd(top)
                  /\ stack' = TL(stack)
                  /\ IF low < high
                     THEN mid' = (low + high) \div 2
                          /\ pc' = "Sort"
                          /\ stack' = <<<<low, mid>>, <<mid+1, high>> >> \o stack'
                     ELSE pc' = "Merge"
         \/ /\ stack = <<>>
            /\ pc' = "Done"
    [] pc = "Merge" ->
         /\ i' = low
         /\ j' = mid + 1
         /\ k' = low
         /\ pc' = "CopyToBuffer"
    [] pc = "CopyToBuffer" ->
         \/ /\ k <= high
            /\ IF i > mid
               THEN b[k]' = a[j]
                    /\ j' = j + 1
               ELSE IF j > high
                    THEN b[k]' = a[i]
                         /\ i' = i + 1
                    ELSE IF a[i] < a[j]
                         THEN b[k]' = a[i]
                              /\ i' = i + 1
                         ELSE b[k]' = a[j]
                              /\ j' = j + 1
            /\ k' = k + 1
            /\ pc' = "CopyToBuffer"
         \/ /\ k > high
            /\ i \le mid
            /\ b[k]' = a[i]
            /\ i' = i + 1
            /\ k' = k + 1
            /\ pc' = "CopyToBuffer"
         \/ /\ k > high
            /\ j \le high
            /\ b[k]' = a[j]
            /\ j' = j + 1
            /\ k' = k + 1
            /\ pc' = "CopyToBuffer"
         \/ /\ k > high
            /\ i > mid
            /\ j > high
            /\ a' = [k \in low..high |-> b[k]]
            /\ pc' = "Sort"

Spec ==
    /\ Init
    /\ [][Next]_<<pc, i, j, k, low, high, mid, a, b, stack>>
    /\ WF_[Next]_<<pc>>

Sorted(seq) == \A i \in 1..Len(seq)-1 : seq[i] <= seq[i+1]

Termination ==
    <>[](pc = "Done")

Safety ==
    [](pc # "Done" => Sorted(a))

=============================================================================