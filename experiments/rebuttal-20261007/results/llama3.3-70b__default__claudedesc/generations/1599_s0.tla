```tla
MODULE LamportFastMutualExclusion
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, b, j, pc

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 1..N |-> FALSE]
  /\ j = [i \in 1..N |-> 0]
  /\ pc = [i \in 1..N |-> "noncritical"]

Next ==
  \/ \E i \in 1..N :
      /\ pc[i] = "noncritical"
      /\ b' = [b EXCEPT ![i] = TRUE]
      /\ x' = i
      /\ y' = y
      /\ j' = [j EXCEPT ![i] = 0]
      /\ pc' = [pc EXCEPT ![i] = "fast_path"]
  \/ \E i \in 1..N :
      /\ pc[i] = "fast_path"
      /\ x = i
      /\ y = 0
      /\ y' = i
      /\ b' = b
      /\ x' = x
      /\ j' = [j EXCEPT ![i] = 1]
      /\ pc' = [pc EXCEPT ![i] = "critical"]
  \/ \E i \in 1..N :
      /\ pc[i] = "fast_path"
      /\ x /= i
      /\ b' = [b EXCEPT ![i] = FALSE]
      /\ y' = y
      /\ x' = x
      /\ j' = [j EXCEPT ![i] = 0]
      /\ pc' = [pc EXCEPT ![i] = "slow_path"]
  \/ \E i \in 1..N :
      /\ pc[i] = "slow_path"
      /\ \A k \in 1..N : ~b[k]
      /\ y' = y
      /\ b' = b
      /\ x' = x
      /\ j' = [j EXCEPT ![i] = 0]
      /\ pc' = [pc EXCEPT ![i] = "l4"]
  \/ \E i \in 1..N :
      /\ pc[i] = "l4"
      /\ y = i
      /\ b' = b
      /\ x' = x
      /\ j' = [j EXCEPT ![i] = 0]
      /\ pc' = [pc EXCEPT ![i] = "critical"]
  \/ \E i \in 1..N :
      /\ pc[i] = "l4"
      /\ y /= i
      /\ b' = b
      /\ x' = x
      /\ j' = [j EXCEPT ![i] = 0]
      /\ pc' = [pc EXCEPT ![i] = "noncritical"]
  \/ \E i \in 1..N :
      /\ pc[i] = "critical"
      /\ y' = 0
      /\ b' = [b EXCEPT ![i] = FALSE]
      /\ x' = x
      /\ j' = [j EXCEPT ![i] = 0]
      /\ pc' = [pc EXCEPT ![i] = "noncritical"]

Invariant ==
  \A i, j \in 1..N : i /= j => ~(pc[i] = "critical" /\ pc[j] = "critical")

CondLiveness ==
  \A i \in 1..N :
    WF_vars(Next) =>
      (\A self \in 1..N : pc[self] /= "noncritical") =>
        <>(\E j \in 1..N : pc[j] = "critical")

FairSpec ==
  /\ [][Init]_x_y_b_j_pc
  /\ [][Next]_x_y_b_j_pc
  /\ CondLiveness

THEOREM Invariant =>
  FairSpec => []Invariant
THEOREM FairSpec => CondLiveness
```