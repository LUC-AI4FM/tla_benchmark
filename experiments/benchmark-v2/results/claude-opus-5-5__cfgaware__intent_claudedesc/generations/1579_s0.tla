------------------------------ MODULE TokenRing ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, K

ASSUME NAssumption == N \in Nat \ {0}
ASSUME KAssumption == K \in Nat /\ K > N

Procs  == 0 .. N-1
Values == 0 .. K-1

VARIABLES c

vars == << c >>

TypeOK == c \in [Procs -> Values]

Init == c \in [Procs -> Values]

\* Process 0 creates (re-issues) the token by incrementing its value.
CreateToken ==
  /\ c[0] = c[N-1]
  /\ c' = [c EXCEPT ![0] = (c[N-1] + 1) % K]

\* Ordinary process i copies its predecessor's value.
PassToken(i) ==
  /\ i # 0
  /\ c[i] # c[i-1]
  /\ c' = [c EXCEPT ![i] = c[i-1]]

Act(i) == IF i = 0 THEN CreateToken ELSE PassToken(i)

Next == \E i \in Procs : Act(i)

Spec == Init /\ [][Next]_vars /\ \A i \in Procs : WF_vars(Act(i))

-----------------------------------------------------------------------------

\* Process i holds the token iff it is enabled to act.
HasToken(i) == IF i = 0 THEN c[0] = c[N-1] ELSE c[i] # c[i-1]

Holders == { i \in Procs : HasToken(i) }

\* Safety: at least one process always holds the token.
SomeoneHoldsToken == \E i \in Procs : HasToken(i)

\* Exactly one process holds the token.
SingleToken == Cardinality(Holders) = 1

\* Liveness: eventually exactly one process holds the token, forever.
EventuallyJustOneHoldsToken == <>[]SingleToken

\* The number of token holders is always between 1 and N.
PossibleCounts == Cardinality(Holders) \in 1 .. N

\* The token keeps circulating: every process holds it infinitely often.
TokenPasses == \A i \in Procs : []<>HasToken(i)

_POSSIBLE ==
  /\ []SomeoneHoldsToken
  /\ []PossibleCounts
  /\ EventuallyJustOneHoldsToken
  /\ TokenPasses

THEOREM Spec => []TypeOK
THEOREM Spec => []SomeoneHoldsToken
THEOREM Spec => EventuallyJustOneHoldsToken
=============================================================================