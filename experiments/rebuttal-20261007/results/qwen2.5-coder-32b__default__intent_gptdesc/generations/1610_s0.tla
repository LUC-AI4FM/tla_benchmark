------------------------------- MODULE QuickSortSpec -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N, DOMAIN

VARIABLES array, pendingIntervals

Init == /\ array \in [1..N -> DOMAIN]
        /\ pendingIntervals = {[1, N]}

Next ==
    \/ /\ pendingIntervals /= {}
       /\ CHOOSE interval \in pendingIntervals:
            LET lo == interval[1]
                hi == interval[2]
            IN
            /\ lo < hi
            /\ \E p \in lo..hi-1:
                 LET newLeft  == [lo..p -> array[lo..p]]
                     newRight == [p+1..hi -> array[p+1..hi]]
                     pivot    == array[p+1]
                 IN
                 /\ array' = [array EXCEPT ![lo..hi] = <<newLeft, pivot, newRight>>]
                 /\ pendingIntervals' = (pendingIntervals \ {interval}) \cup {[lo, p], [p+1, hi]}
        \/ /\ pendingIntervals /= {}
           /\ CHOOSE interval \in pendingIntervals:
                LET lo == interval[1]
                    hi == interval[2]
                IN
                /\ lo >= hi
                /\ array' = array
                /\ pendingIntervals' = pendingIntervals \ {interval}

Spec ==
    /\ Init
    /\ [][Next]_<<array, pendingIntervals>>
    /\ WF_next(<<array, pendingIntervals>>)

Inv1 == \/ pendingIntervals = {}
          \/ \A interval \in pendingIntervals:
               LET lo == interval[1]
                   hi == interval[2]
               IN
               lo <= hi

Inv2 ==
    \A i \in 1..N: \A j \in 1..N: array[i] = array'[j] => \E k \in 1..N: array[k] = array'[i]

Inv3 ==
    \A interval \in pendingIntervals:
        LET lo == interval[1]
            hi == interval[2]
        IN
        \A i \in lo..hi: array[i] = array'[i]

OrderingProgress ==
    /\ pendingIntervals = {}
    /\ \A i, j \in 1..N: i <= j => array[i] <= array[j]

Termination ==
    <>[] (pendingIntervals = {})

WF_next(vars) == WF_vars(Next, vars)

=============================================================================