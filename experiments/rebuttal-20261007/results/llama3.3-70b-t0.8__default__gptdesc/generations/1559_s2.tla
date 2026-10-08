```
MODULE Lock
EXTENDS Integers, Sequences, Stuttering

CONSTANTS NumProcs
VARIABLES turn, h_turn, pc, s, locked

Init ==
  /\ turn = 1
  /\ h_turn = <<>>
  /\ pc = [i \in 1..NumProcs |-> "N"]
  /\ s = FALSE
  /\ locked = FALSE

Next ==
  \/ (pc[1] = "N") /\ (pc' = [pc EXCEPT ![1] = "T"])
    /\ (h_turn' = Append(h_turn, 1))
    /\ (turn' = 2)
    /\ (s' = TRUE)
    /\ (locked' = locked)
  \/ (pc[1] = "T") /\ (pc' = [pc EXCEPT ![1] = "L"])
    /\ (h_turn' = h_turn)
    /\ (turn' = turn)
    /\ (s' = FALSE)
    /\ (locked' = TRUE)
  \/ (pc[2] = "N") /\ (pc' = [pc EXCEPT ![2] = "T"])
    /\ (h_turn' = Append(h_turn, 2))
    /\ (turn' = 1)
    /\ (s' = TRUE)
    /\ (locked' = locked)
  \/ (pc[2] = "T") /\ (pc' = [pc EXCEPT ![2] = "L"])
    /\ (h_turn' = h_turn)
    /\ (turn' = turn)
    /\ (s' = FALSE)
    /\ (locked' = TRUE)
  \/ (pc[1] = "L") /\ (pc' = [pc EXCEPT ![1] = "N"])
    /\ (h_turn' = h_turn)
    /\ (turn' = turn)
    /\ (s' = s)
    /\ (locked' = FALSE)
  \/ (pc[2] = "L") /\ (pc' = [pc EXCEPT ![2] = "N"])
    /\ (h_turn' = h_turn)
    /\ (turn' = turn)
    /\ (s' = s)
    /\ (locked' = FALSE)

Spec ==
  Init /\ [][Next]_<<pc, h_turn, turn, s, locked>>

THEOREM Spec => []~(locked' = TRUE) /\ WF-vars(Next)_(pc, h_turn, turn, s, locked)
```
Note: In the THEOREM statement, I used `WF-vars` to specify weak fairness for all variables. If you need strong fairness instead, replace it with `SF-vars`.