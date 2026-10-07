```
MODULE DijkstraTokenRing
EXTENDS Integers, FiniteSets

CONSTANTS N, K
VARIABLES M, pc

Init ==
  /\ M \in [0..N-1 -> 0..K-1]
  /\ pc = [i \in 0..N-1 |-> "guard"]

Next ==
  \/ \E i \in 0..N-1 :
      IF pc[i] = "guard"
      THEN
        /\ pc' = [pc EXCEPT ![i] = "assign"]
        /\ IF i = 0
          THEN M' = [M EXCEPT ![0] = (M[0] + 1) % K]
          ELSE M' = [M EXCEPT ![i] = M[i-1]]
      ELSE
        /\ pc' = [pc EXCEPT ![i] = "guard"]
        /\ M' = M

Spec ==
  Init /\ [][Next]_<<M, pc>>
  /\ WF_vars(<<M, pc>>)

SomeoneHoldsToken ==
  \E i \in 0..N-1 :
    IF i = 0
    THEN M[0] = M[N-1]
    ELSE M[i] # M[(i-1) % N]

EventuallyJustOneHoldsToken ==
  <>[]<<\E i \in 0..N-1 : 
      (IF i = 0 THEN M[0] = M[N-1] ELSE M[i] # M[(i-1) % N])
      /\ \A j \in 0..N-1 \ {i} :
          (IF j = 0 THEN M[j] # M[N-1] ELSE M[j] = M[(j-1) % N])>>

THEOREM Spec => []SomeoneHoldsToken
THEOREM Spec => EventuallyJustOneHoldsToken

```
Note: The `WF_vars` operator is used to specify weak fairness for all processes. This ensures that every enabled process will eventually take a step. 

Also, note that the `THEOREM` statements are used to assert the safety and liveness properties of the system. These can be checked using the TLC model checker.