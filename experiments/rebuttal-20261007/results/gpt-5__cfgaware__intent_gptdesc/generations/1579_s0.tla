---- MODULE TokenRing ----
EXTENDS Naturals, Integers

CONSTANTS N, K

ASSUME /\ N \in Nat /\ N > 0
       /\ K \in Nat /\ K > N

VARIABLES c

Proc == 0..(N-1)
Val  == 0..(K-1)

Init == c \in [Proc -> Val]

Holds(i) ==
  IF i = 0
    THEN c[0] = c[N-1]
    ELSE c[i] /= c[i-1]

TokenHolders == { i \in Proc : Holds(i) }

Inc0 ==
  /\ Holds(0)
  /\ c' = [c EXCEPT ![0] = (c[0] + 1) % K]

Copy(i) ==
  /\ i \in 1..(N-1)
  /\ Holds(i)
  /\ c' = [c EXCEPT ![i] = c[i-1]]

Next == Inc0 \/ (\E i \in 1..(N-1) : Copy(i))

Fairness ==
  /\ WF_c(Inc0)
  /\ \A i \in 1..(N-1) : WF_c(Copy(i))

Spec == Init /\ [][Next]_c /\ Fairness

SomeoneHoldsToken == TokenHolders /= {}

ExactlyOneHolds ==
  \E i \in Proc :
    Holds(i) /\ \A j \in Proc : j /= i => ~Holds(j)

EventuallyJustOneHoldsToken == <>[] ExactlyOneHolds
====