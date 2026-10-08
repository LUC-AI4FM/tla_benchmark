```
MODULE LockProtocol
EXTENDS Integers, Sequences, Stuttering

CONSTANTS NumProcs
VARIABLES h_turn, s, pc, locked

Init ==
  /\ h_turn = <<>>
  /\ s = FALSE
  /\ pc = [i \in 1..NumProcs |-> "idle"]
  /\ locked = FALSE

Next ==
  /\ (pc[1] = "idle") => 
    /\ pc' = [pc EXCEPT ![1] = "trying"]
    /\ h_turn' = Append(h_turn, 1)
    /\ s' = TRUE
    /\ locked' = locked
  /\ (pc[2] = "idle") => 
    /\ pc' = [pc EXCEPT ![2] = "trying"]
    /\ h_turn' = Append(h_turn, 2)
    /\ s' = TRUE
    /\ locked' = locked
  /\ (pc[1] = "trying" /\ h_turn[Len(h_turn)] = 1) =>
    /\ pc' = [pc EXCEPT ![1] = "critical"]
    /\ h_turn' = h_turn
    /\ s' = FALSE
    /\ locked' = TRUE
  /\ (pc[2] = "trying" /\ h_turn[Len(h_turn)] = 2) =>
    /\ pc' = [pc EXCEPT ![2] = "critical"]
    /\ h_turn' = h_turn
    /\ s' = FALSE
    /\ locked' = TRUE
  /\ (pc[1] = "critical") => 
    /\ pc' = [pc EXCEPT ![1] = "idle"]
    /\ h_turn' = h_turn
    /\ s' = FALSE
    /\ locked' = FALSE
  /\ (pc[2] = "critical") =>
    /\ pc' = [pc EXCEPT ![2] = "idle"]
    /\ h_turn' = h_turn
    /\ s' = FALSE
    /\ locked' = FALSE

Spec == Init /\ [][Next]_<<h_turn, s, pc, locked>>
  
Fairness == WF_vars(Next, <<h_turn, s, pc, locked>>)

THEOREM Spec => []~(locked /\ (pc[1] = "critical" /\ pc[2] = "critical"))
```