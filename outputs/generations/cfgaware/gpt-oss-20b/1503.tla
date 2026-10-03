------------------------------ MODULE SmallSM ------------------------------
EXTENDS Naturals, Integers, TLC

VARIABLES x

Op(S, P, Q) == { s \in S : P[s] /\ Q[s, TRUE] }

Init == x \in Op({1,2,3,4,5}, λs: s > 1, λs,b: b /\ (s Mod 2 = 1))

Next == UNCHANGED x

==============================================================================