---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLES flag, reg1, reg2, cs

Invariant == 
  /\ flag \in [1..N -> BOOLEAN]
  /\ reg1 \in 1..N
  /\ reg2 \in 1..N
  /\ cs \in [1..N -> BOOLEAN]

TypeOK == 
  /\ flag = [i \in 1..N |-> FALSE]
  /\ reg1 = 0
  /\ reg2 = 0
  /\ cs = [i \in 1..N |-> FALSE]

Init == TypeOK

Next(i \in 1..N) == 
  \/ \* non-critical section to trying to acquire lock
      cs[i] = FALSE
      /\ flag' = [flag EXCEPT ![i] = TRUE]
      /\ reg1' = reg1
      /\ reg2' = reg2
      /\ cs' = cs
  \/ \* write reg1
      flag[i] = TRUE
      /\ reg1 = 0
      /\ reg1' = i
      /\ reg2' = reg2
      /\ flag' = flag
      /\ cs' = cs
  \/ \* check contention and potentially wait or retry
      flag[i] = TRUE
      /\ reg1 = i
      /\ reg2 = 0
      /\ (reg2' = i 
          /\ flag' = flag
          /\ cs' = cs
          /\ reg1' = reg1)
      \/ (reg2' = reg2
          /\ flag' = flag
          /\ cs' = [cs EXCEPT ![i] = TRUE]
          /\ reg1' = 0)
  \/ \* enter critical section if no contention
      flag[i] = TRUE
      /\ reg1 = i
      /\ reg2 = i
      /\ (reg1' = reg1
          /\ reg2' = reg2
          /\ flag' = flag
          /\ cs' = [cs EXCEPT ![i] = TRUE])
  \/ \* exit critical section and reset state
      cs[i] = TRUE
      /\ flag' = [flag EXCEPT ![i] = FALSE]
      /\ reg1' = 0
      /\ reg2' = 0
      /\ cs' = [cs EXCEPT ![i] = FALSE]

Next == \E i \in 1..N : Next(i)

Spec == Init /\ [][Next]_<<flag, reg1, reg2, cs>>

CondLiveness == 
  \A i \in 1..N : WF(Next(i), Spec)

FairSpec == Spec /\ CondLiveness

THEOREM Spec => []Invariant
=============================================================================