```
MODULE TokenRing
EXTENDS Integers

CONSTANTS N, M
VARIABLES counters, tokenPresent

Init ==
  /\ counters \in [1..N -> 0..M-1]
  /\ tokenPresent \in [1..N -> {TRUE, FALSE}]

Next ==
  /\ IF (tokenPresent[1] = TRUE)
     THEN /\ counters' = [counters EXCEPT ![1] = (counters[N] + 1) % M]
          /\ tokenPresent' = [tokenPresent EXCEPT ![1] = FALSE]
     ELSE
       /\ counters' = [counters EXCEPT ![i \in 2..N] = IF (counters[<<i-1>>] # counters[i])
                                                         THEN counters[<<i-1>>]
                                                         ELSE counters[i]]
       /\ tokenPresent' = [tokenPresent EXCEPT ![i \in 2..N] = IF (counters[<<i-1>>] # counters[i])
                                                                   THEN TRUE
                                                                   ELSE tokenPresent[i]]

Spec == Init /\ [][Next]_<<counters, tokenPresent>>
StabilizationInvariant == \E i \in 1..N : tokenPresent[i] = TRUE
UniqueTokenProperty == []<>\<>StabilizationInvariant

THEOREM Spec => []<>StabilizationInvariant
THEOREM Spec => UniqueTokenProperty
```