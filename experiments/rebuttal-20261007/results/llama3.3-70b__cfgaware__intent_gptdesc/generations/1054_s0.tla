---------------------------- MODULE TokenRing ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N, M
VARIABLE counters, source, tokenPresent

AssumeNAndMBounds == N > 0 /\ M > 1

TypeInvariant == counters \in [1..N -> 0..M-1]

source == 1

Init == (* Initial state: every process counter is an arbitrary value *)
        /\ counters \in [1..N -> 0..M-1]
        /\ tokenPresent = FALSE

NextCounter(p) == IF p = source THEN (counters[p] + 1) % M ELSE counters[THE p' : p' = (p - 1) % N + 1]

InjectToken == 
  /\ source = 1
  /\ counters' = [counters EXCEPT ![source] = NextCounter(source)]
  /\ tokenPresent' = TRUE

PassToken(p) == 
  /\ p \in 2..N
  /\ counters[THE p' : p' = (p - 1) % N + 1] # counters[p]
  /\ counters' = [counters EXCEPT ![p] = NextCounter(p)]
  /\ tokenPresent' = tokenPresent

NoOp == 
  /\ counters' = counters
  /\ tokenPresent' = tokenPresent

Next == 
  \/ InjectToken
  \/ \E p \in 2..N : PassToken(p)
  \/ NoOp

Spec == Init /\ [][Next]_<<counters, tokenPresent>>

Safety == []TypeInvariant

SelfStabilization == <>[]\A p, q \in 1..N : 
                      (counters[p] = counters[q]) \/ 
                      ((counters[p] = counters[q] + 1) % M) \/ 
                      ((counters[p] = counters[q] - 1) % M)

THEOREM Spec => []Safety
THEOREM Spec => SelfStabilization

Fairness == WF_<<counters, tokenPresent>>(Next)
=============================================================================