----------------------------- MODULE TokenRing -----------------------------
EXTENDS Integers

CONSTANTS N, M, Source

ASSUME
  /\ N \in Nat /\ N >= 2
  /\ M \in Nat /\ M >= N
  /\ Source \in 0..(N-1)

Proc == 0..(N-1)
Val  == 0..(M-1)

Prev(i) == IF i = 0 THEN N - 1 ELSE i - 1

VARIABLES c

TypeOK == c \in [Proc -> Val]

Init == TypeOK

Copy(i) ==
  /\ i \in Proc \ {Source}
  /\ c[i] # c[Prev(i)]
  /\ c' = [c EXCEPT ![i] = c[Prev(i)]]

SourceCopy ==
  /\ c[Source] # c[Prev(Source)]
  /\ c' = [c EXCEPT ![Source] = c[Prev(Source)]]

SourceInject ==
  /\ c[Source] = c[Prev(Source)]
  /\ c' = [c EXCEPT ![Source] = (c[Source] + 1) % M]

Next ==
  SourceInject
  \/ SourceCopy
  \/ (\E i \in Proc \ {Source}: Copy(i))

BoundarySet == { i \in Proc : c[i] # c[Prev(i)] }

CanonicalUniqueToken ==
  \E b \in Proc:
    /\ BoundarySet = {b}
    /\ c[b] = (c[Prev(b)] + 1) % M

Safety == []TypeOK

SelfStabilization == <>[]CanonicalUniqueToken

Spec ==
  /\ Init
  /\ [][Next]_c
  /\ WF_c(SourceInject)
  /\ WF_c(SourceCopy)
  /\ \A i \in Proc \ {Source}: WF_c(Copy(i))
============================================================================