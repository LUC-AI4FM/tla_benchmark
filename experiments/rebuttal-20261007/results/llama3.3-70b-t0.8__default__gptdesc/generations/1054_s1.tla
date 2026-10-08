```
MODULE TokenRing
EXTENDS Integers, FiniteSets

CONSTANTS N, M
VARIABLES counters, tokenPresent

Init ==
  /\ counters \in [1..N -> 0..M-1]
  /\ tokenPresent \in [1..N -> {True, False}]

Next ==
  /\ IF (node = 1) THEN
      /\ counters' = [counters EXCEPT ![1] = (counters[1] + 1) % M]
      /\ tokenPresent' = [tokenPresent EXCEPT ![1] = True]
    ELSE
      /\ counters' = 
        IF (counters[node-1] # counters[node]) THEN
          [counters EXCEPT ![node] = counters[node-1]]
        ELSE
          counters
      /\ tokenPresent' = 
        IF (counters[node-1] # counters[node]) THEN
          [tokenPresent EXCEPT ![node] = True]
        ELSE
          tokenPresent
  /\ OTHERS UNCHANGED

Spec == Init /\ [][Next]_<<counters, tokenPresent>>
Fairness == <<counters, tokenPresent>> \in WeakFairness

StabilizationInv == 
  \E t \in [1..N] : tokenPresent[t] = True

UniqueTokenInv == 
  \A s, t \in [1..N] : (tokenPresent[s] /\ tokenPresent[t]) => s = t

TypeOK == 
  /\ N >= 1
  /\ M > 0
  /\ N <= M + 1
  /\ counters \in [1..N -> 0..M-1]
  /\ tokenPresent \in [1..N -> {True, False}]

THEOREM Spec => []TypeOK
THEOREM Spec => StabilizationInv
THEOREM Spec => UniqueTokenInv
THEOREM Spec => <>[]StabilizationInv
THEOREM Spec => WF_<<counters, tokenPresent>>_(Next)
```