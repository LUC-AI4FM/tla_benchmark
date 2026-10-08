------------------------------- MODULE DijkstraTokenRing -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, K

VARIABLES values

Init == /\ values \in [0..N-1 -> 0..K-1]
        /\ (\E i \in 0..N-1 : values[i] = values[SUBSET (i-1) % N])

Next ==
    \/ \E i \in 0..N-1 :
        LET pred == (i-1) % N
            succ == (i+1) % N
            currVal == values[i]
            predVal == values[pred]
        IN /\ values' = [values EXCEPT ![i] = IF i = 0 THEN IF currVal = predVal THEN (currVal + 1) % K ELSE currVal
                                                      ELSE IF currVal # predVal THEN predVal ELSE currVal]
           /\ UNCHANGED << >> 
    \/ UNCHANGED values

WF_Values ==
    WF_vars(Next, <<values>>)

Spec ==
    \* Weak fairness for all processes
    WF_Values
    /\ Init
    /\ [][Next]_<<values>>

SingleToken ==
    \A s \in State : (Cardinality({i \in 0..N-1 : s.values[i] = s.values[(i+1) % N]}) = 1)

Convergence ==
    <>(\E i \in 0..N-1 : values[i] # values[(i+1) % N])

THEOREM Spec => []SingleToken
THEOREM Spec => <>Convergence

=============================================================================