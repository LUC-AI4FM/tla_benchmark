------------------------------- MODULE DijkstraTokenRing -------------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANTS N, K

VARIABLES values

Init == /\ N \in Nat
        /\ K \in Nat
        /\ N > 0
        /\ K > N
        /\ values \in [0..N-1 -> 0..K-1]

Next == 
    \/ /\ \E i \in 0..N-1 : (i = 0) /\ values[i] = values[N-1]
         /\ values' = [values EXCEPT ![0] = (values[0] + 1) % K]
       \/ /\ \E i \in 0..N-1 : (i > 0) /\ values[i] # values[(i - 1)]
          /\ values' = [values EXCEPT ![i] = values[(i - 1)]]

Spec == Init /\ [][Next]_<<values>>

WF_spec == WF_next(<<values>>)

TypeOK == /\ N \in Nat
         /\ K \in Nat
         /\ N > 0
         /\ K > N
         /\ values \in [0..N-1 -> 0..K-1]

TokenHolder ==
    \E i \in 0..N-1 : (i = 0 /\ values[i] = values[N-1])
                    \/ (i > 0 /\ values[i] # values[(i - 1)])

ExactlyOneTokenHolder ==
    \A i \in 0..N-1, j \in 0..N-1 :
        (i = j) \/ ~((values[i] = values[N-1] /\ i = 0)
                    \/ (values[j] # values[(j - 1)] /\ j > 0))

Inv == TypeOK /\ TokenHolder

SpecWithInvariants == Spec /\ [](Inv)

Liveness ==
    \/ \A s, t \in State : s /= t => <>[](ExactlyOneTokenHolder)

THEOREM SpecWithInvariants => []<>(ExactlyOneTokenHolder)

=============================================================================