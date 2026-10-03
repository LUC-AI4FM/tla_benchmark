---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers

CONSTANT N, M
VARIABLE x, y, b, pc

vars == <<x, y, b, pc>>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = FALSE
  /\ pc = [i \in 1..N |-> "Start"]

Next ==
  \/ \E i \in 1..M : Next_i(i)
  \/ \E j \in (M+1)..N : Next_j(j)

Next_i(i) ==
  pc[i] = "Start" /\ x' = i /\ pc' = [pc EXCEPT ![i] = "Try"]
  \/ pc[i] = "Try" /\ y' = i /\ pc' = [pc EXCEPT ![i] = "Wait"]
  \/ pc[i] = "Wait" /\ b' = TRUE /\ pc' = [pc EXCEPT ![i] = "Crit"]
  \/ pc[i] = "Crit" /\ x' = 0 /\ y' = 0 /\ b' = FALSE /\ pc' = [pc EXCEPT ![i] = "Start"]

Next_j(j) ==
  pc[j] = "Start" /\ x' = j /\ pc' = [pc EXCEPT ![j] = "Try"]
  \/ pc[j] = "Try" /\ y' = j /\ pc' = [pc EXCEPT ![j] = "Wait"]
  \/ pc[j] = "Wait" /\ b' = TRUE /\ pc' = [pc EXCEPT ![j] = "Crit"]
  \/ pc[j] = "Crit" /\ x' = 0 /\ y' = 0 /\ b' = FALSE /\ pc' = [pc EXCEPT ![j] = "Start"]

Spec == Init /\ [][Next]_vars
           /\ WF_vars(Next_i(1)) /\ ... /\ WF_vars(Next_i(M))
           /\ WF_vars(Next_j(M+1)) /\ ... /\ WF_vars(Next_j(N))

Invariant == \A i, j \in 1..N : i # j => ~(pc[i] = "Crit" /\ pc[j] = "Crit")

Liveness == <>[]<>(\E i \in 1..N : pc[i] = "Crit")
=============================================================================