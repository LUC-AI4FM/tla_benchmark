```
MODULE Quicksort
EXTENDS Integers, Sequences

CONSTANTS N
VARIABLES pc, S, arr

Init ==
  /\ pc = "Start"
  /\ S = {<<1, N>>}
  /\ arr \in [1..N -> 1..N]

qs1 ==
  /\ pc = "Start"
  /\ \E interval \in S :
    /\ \E pivot \in interval :
      /\ Let
            left == <<i \in 1..(pivot-1) : TRUE>>
            right == <<i \in (pivot+1)..N : TRUE>>
          In
            /\ arr' = [a \in 1..N |-> IF a \in left THEN a ELSE IF a = pivot THEN pivot ELSE IF a \in right THEN a ELSE undef]
            /\ pc' = "Start"
            /\ S' = (S \ {interval}) \cup {<<interval[1], pivot-1>>, <<pivot+1, interval[2]>>}
      /\ UNCHANGED arr

Next ==
  /\ pc = "Start" => qs1
  /\ pc = "Done" => UNCHANGED <<pc, S, arr>>

Spec == Init /\ [][Next]_<<pc, S, arr>>
Termination == <>(pc = "Done")

THEOREM Spec => []Termination
Fairness == SF_(<<pc, S, arr>>)(Next)
```
Note: I assume that the `SF_` fairness condition is used to specify weak fairness. Also, note that this specification does not explicitly define what it means for an array to satisfy the "partition ordering constraints" around a pivot, as this was not specified in the problem description. In practice, you would need to add additional conditions to the `qs1` action to ensure that the partitioning is done correctly.