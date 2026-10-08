```
MODULE LockProtocol
EXTENDS Integers, Sequences, Stuttering

CONSTANTS NumProcs
VARIABLES h_turn, s, turn, pc, locked

Init ==
  /\ h_turn = <<>>
  /\ s = FALSE
  /\ turn = 1
  /\ pc = [i \in 1..NumProcs |-> "N"]
  /\ locked = FALSE

Next ==
  /\ (pc[1] = "N") => 
    /\ IF s THEN
      /\ h_turn := Append(h_turn, 2)
      /\ turn := 2
      /\ pc := [pc EXCEPT ![1] = "T1"]
      ELSE
      /\ h_turn := Append(h_turn, 1)
      /\ turn := 1
      /\ pc := [pc EXCEPT ![1] = "T1"]
    /\ (pc[2] = "N") => 
      /\ IF s THEN
      /\ h_turn := Append(h_turn, 1)
      /\ turn := 1
      /\ pc := [pc EXCEPT ![2] = "T1"]
      ELSE
      /\ h_turn := Append(h_turn, 2)
      /\ turn := 2
      /\ pc := [pc EXCEPT ![2] = "T1"]
    /\ (pc[1] = "T1") => 
      /\ IF turn = 1 THEN
      /\ locked := TRUE
      /\ pc := [pc EXCEPT ![1] = "C"]
      ELSE
      /\ pc := [pc EXCEPT ![1] = "W"]
    /\ (pc[2] = "T1") => 
      /\ IF turn = 2 THEN
      /\ locked := TRUE
      /\ pc := [pc EXCEPT ![2] = "C"]
      ELSE
      /\ pc := [pc EXCEPT ![2] = "W"]
    /\ (pc[1] = "W") => 
      /\ IF turn = 1 THEN
      /\ locked := TRUE
      /\ pc := [pc EXcept ![1] = "C"]
    /\ (pc[2] = "W") => 
      /\ IF turn = 2 THEN
      /\ locked := TRUE
      /\ pc := [pc EXCEPT ![2] = "C"]
    /\ (locked) =>
      /\ OR [i \in 1..NumProcs |-> pc[i] = "C"]

Spec == Init /\ [][Next]_<<h_turn, s, turn, pc, locked>>
Inv == locked => OR [i \in 1..NumProcs |-> pc[i] = "C"]
Fairness == SF_VARIABLES (pc)

THEOREM Spec => []Inv
```
Note: This TLA+ module assumes the existence of a `Stuttering` module that provides the necessary definitions for stuttering and history tracking. The `Sequences` and `Integers` modules are part of the TLA+ standard library.