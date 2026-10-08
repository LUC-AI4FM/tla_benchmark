MODULE TokenRing

EXTENDS Naturals, Sequences, TLC

CONSTANTS N, K

VARIABLE counters

Pred(i) == (i - 1 + N) Mod N

TokenHolder(i) == counters[i] # counters[Pred(i)]

ExactlyOneToken ==
    \E i \in 0..N-1 :
        TokenHolder(i)
        /\ (\A j \in 0..N-1 : j /= i => counters[j] = counters[Pred(j)])

Init ==
    counters \in [0..N-1 -> 0..K-1]

Step_i(i) ==
    LET newVal == IF i = 0 THEN (counters[i] + 1) Mod K ELSE counters[Pred(i)] IN
    /\ counters' = [counters EXCEPT ![i] = newVal]
    /\ (i = 0 \/ TokenHolder(i))

Next ==
    \E i \in 0..N-1 : Step_i(i)

TokenExistence == \E i \in 0..N-1 : TokenHolder(i)

Spec ==
    Init
    /\ [][Next]_counters
    /\ WF_vars(Next)
    /\ TokenExistence
    /\ <>[] ExactlyOneToken
    /\ (N > 0 /\ K > N)

END MODULE