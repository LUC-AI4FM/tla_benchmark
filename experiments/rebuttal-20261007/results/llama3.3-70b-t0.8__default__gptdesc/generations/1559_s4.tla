```
MODULE LockProtocol
EXTENDS Integers, Stuttering

CONSTANTS NumProcs
VARIABLES h_turn, s, turn, pc

Init == (h_turn = <<>>) /\ (s = 0) /\ (turn = 1) /\ (pc = [i \in 1..NumProcs |-> "out"])

Next == 
  /\ (pc' = [i \in 1..NumProcs |-> IF pc[i] = "out" THEN "try" ELSE pc[i]])
  /\ (s' = s + 1)
  /\ (IF turn = 1 THEN h_turn' = Append(h_turn, 1) ELSE h_turn' = Append(h_turn, 2))
  /\ (turn' = IF turn = 1 THEN 2 ELSE 1)

Spec == Init /\ [][Next]_<<h_turn, s, turn, pc>>

THEOREM Spec => []<>(pc[1] = "in")
THEOREM Spec => <>[](pc[1] = "out")

Fairness == <>[]<(pc' = [i \in 1..NumProcs |-> IF pc[i] = "try" THEN "in" ELSE pc[i]])>
```
Note: `Stuttering` module should be defined elsewhere, this specification extends it. The above code assumes that the `Integers` and `Stuttering` modules are already defined and available for extension.