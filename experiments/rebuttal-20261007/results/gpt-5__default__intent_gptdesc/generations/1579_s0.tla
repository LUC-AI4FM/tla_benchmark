---- MODULE TokenRing ----
EXTENDS Naturals, Integers

CONSTANTS N, K

ASSUME /\ N \in Nat /\ N > 0
       /\ K \in Nat /\ K > N

VARIABLES c

Proc == 0..(N - 1)

Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

TypeInv == c \in [Proc -> 0..(K - 1)]

Holder(i) == IF i = 0 THEN c[i] = c[Pred(i)] ELSE c[i] # c[Pred(i)]

TokenHolders == { i \in Proc : Holder(i) }

Incr(x) == IF x = K - 1 THEN 0 ELSE x + 1

Init == TypeInv

Inc0 == /\ Holder(0)
        /\ c' = [c EXCEPT ![0] = Incr(@)]

Copy(i) == /\ i \in Proc
           /\ i # 0
           /\ Holder(i)
           /\ c' = [c EXCEPT ![i] = c[Pred(i)]]

Next == Inc0 \/ (\E i \in Proc: Copy(i))

Spec == /\ Init
        /\ [][Next]_c
        /\ WF_c(Inc0)
        /\ \A i \in Proc \ {0}: WF_c(Copy(i))

\* Safety: token existence (always at least one holder) and type invariant
Safety == [] (TypeInv /\ TokenHolders # {})

\* Exactly one token
OneToken == \E i \in Proc: TokenHolders = {i}

\* Liveness: convergence to a stable single-token regime
Convergence == <>[] OneToken

\* Liveness: the token circulates (process 0 increments infinitely often)
Circulates == []<> Inc0

====