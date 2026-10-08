---------------------------- MODULE Quicksort ----------------------------
EXTENDS Integers, Sequences

CONSTANT N
VARIABLE arr, pendingIntervals

Spec == 
  /\ arr \in Seq(1..N)
  /\ pendingIntervals = {{1, N}}
  /\ [][
      /\ IF pendingIntervals # {}
        THEN 
          /\ LET interval == CHOOSE interval \in pendingIntervals IN
            /\ interval = [lo, hi]
            /\ lo <= hi
            /\ IF lo < hi
              THEN 
                /\ LET p == CHOOSE p \in {i \in Nat : lo <= i < hi} IN
                  /\ arr' = [arr EXCEPT !i = IF i \in [lo..p] 
                                            THEN CHOOSE v \in {arr[j] : j \in [lo..hi]} : 
                                              FORALL k \in [lo..p] : v <= arr[k]
                                            ELSE IF i \in [p+1..hi] 
                                              THEN CHOOSE v \in {arr[j] : j \in [lo..hi]} : 
                                                FORALL k \in [p+1..hi] : arr[k] <= v
                                              ELSE arr[i]]
                  /\ pendingIntervals' = (pendingIntervals \ {interval}) \cup {[lo, p], [p+1, hi]}
              ELSE 
                /\ arr' = arr
                /\ pendingIntervals' = pendingIntervals \ {interval}
        ELSE 
          /\ arr' = arr
          /\ pendingIntervals' = {}
      /\ UNCHANGED <<arr, pendingIntervals>>
    ]

Termination == <>[]pendingIntervals = {}

THEOREM Spec => []Termination

=============================================================================