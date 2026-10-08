------------------------------- MODULE TokenRing -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, K
ASSUME N > 0 /\ K > N

VARIABLES values

Init == /\ values \in [0..N-1 -> 0..K-1]
        /\ values[0] = values[N-1]

Next ==
    \/ /\ values[0] = values[N-1]
       /\ LET newValue == (values[0] + 1) % K
       IN /\ values' = [values EXCEPT ![0] = newValue]
    \/ \E i \in 1..N-1 :
          /\ values[i] # values[i-1]
          /\ values' = [values EXCEPT ![i] = values[i-1]]

Spec ==
    /\ Init
    /\ [][Next]_<<values>>
    /\ WF_next(<<values>>)

TokenHeldByOne ==
    \E i \in 0..N-1 :
        (/\ i = 0 => values[0] = values[N-1])
        /\ (/\ i > 0 => values[i] # values[i-1])

Safety == []<>(\A j \in 0..N-1 : 
                  \/ (j = 0 => values[j] = values[N-1])
                  \/ (j > 0 => values[j] # values[j-1]))

Liveness ==
    <>(/\ TokenHeldByOne
        /\ [](TokenHeldByOne))

THEOREM Spec => []<>(Safety /\ Liveness)
=============================================================================