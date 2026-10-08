------------------------------ MODULE EWD426 ------------------------------

EXTENDS Naturals, Integers, FiniteSets

CONSTANTS N, M

ASSUME /\ N \in Nat /\ M \in Nat
       /\ N > 0 /\ M > 0
       /\ N <= M + 1

VARIABLES c

Indices == 0..(N - 1)
Values  == 0..(M - 1)

TypeOK == c \in [Indices -> Values]

Mod(a, m) == ((a % m) + m) % m

Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

Init == TypeOK

CreateToken ==
  /\ c[0] = c[Pred(0)]
  /\ c' = [c EXCEPT ![0] = Mod(c[0] + 1, M)]

PassToken(i) ==
  /\ i \in 1..(N - 1)
  /\ c[i] # c[Pred(i)]
  /\ c' = [c EXCEPT ![i] = c[Pred(i)]]

Next ==
  CreateToken
  \/ (∃ i \in 1..(N - 1): PassToken(i))

Spec == Init /\ [][Next]_c /\ WF_c(Next)

TokenAt(i) ==
  /\ i \in Indices
  /\ ∀ j \in 0..(i - 1): c[j] = c[0]
  /\ ∀ j \in i..(N - 1): c[j] = Mod(c[0] - 1, M)

Tokens == { i \in Indices : TokenAt(i) }

OneToken == Cardinality(Tokens) = 1

Stab == <>[] OneToken

=============================================================================