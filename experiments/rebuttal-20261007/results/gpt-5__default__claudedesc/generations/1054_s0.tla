---- MODULE DijkstraTokenRing ----
EXTENDS Naturals, Integers, TLC

CONSTANTS N, M

ASSUME
  /\ N \in Nat /\ N > 0
  /\ M \in Nat /\ M > 0
  /\ N <= M + 1

VARIABLES c

Nodes == 0..(N - 1)

TypeOK == c \in [Nodes -> 0..(M - 1)]

Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

Mod(a, m) == ((a % m) + m) % m

Init == TypeOK

CreateToken ==
  /\ c[0] = c[N - 1]
  /\ c' = [c EXCEPT ![0] = Mod(c[0] + 1, M)]

PassToken(i) ==
  /\ i \in 1..(N - 1)
  /\ c[i] # c[Pred(i)]
  /\ c' = [c EXCEPT ![i] = c[Pred(i)]]

Next ==
  CreateToken \/ (\E i \in 1..(N - 1): PassToken(i))

TokDown == Mod(c[0] - 1, M)

TokenAtPos(i) ==
  /\ i \in 0..N
  /\ (\A j \in 0..(i - 1): c[j] = c[0])
  /\ (\A j \in i..(N - 1): c[j] = TokDown)

TokenSet == { i \in 0..N : TokenAtPos(i) }

ExactlyOneToken == Cardinality(TokenSet) = 1

Stab == <>[] ExactlyOneToken

Spec == Init /\ [][Next]_c /\ WF_c(Next)
====