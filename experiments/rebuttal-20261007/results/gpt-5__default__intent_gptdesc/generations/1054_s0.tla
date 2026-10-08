------------------------------ MODULE TokenRing ------------------------------

EXTENDS Integers, FiniteSets

CONSTANTS N, M, Src

ASSUME Bounds ==
  /\ N \in Nat
  /\ N >= 2
  /\ M \in Nat
  /\ M >= N
  /\ Src \in 0..(N - 1)

VARIABLES cnt

Procs  == 0..(N - 1)
Values == 0..(M - 1)

Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1
Succ(i) == (i + 1) % N
Inc(v)  == (v + 1) % M
Dec(v)  == (v - 1) % M

vars == << cnt >>

Init == cnt \in [Procs -> Values]

Copy(i) ==
  /\ i \in Procs \ {Src}
  /\ cnt[i] /= cnt[Pred(i)]
  /\ cnt' = [cnt EXCEPT ![i] = cnt[Pred(i)]]

SourceStep ==
  /\ cnt[Src] = cnt[Pred(Src)]
  /\ cnt' = [cnt EXCEPT ![Src] = Inc(cnt[Src])]

Next ==
  \/ SourceStep
  \/ \E i \in Procs \ {Src} : Copy(i)

TypeOK == cnt \in [Procs -> Values]

NumBoundaries(c) ==
  Cardinality({ i \in Procs : c[i] /= c[Succ(i)] })

UniqueToken(c) ==
  LET B == { i \in Procs : c[i] /= c[Succ(i)] } IN
    /\ Cardinality(B) = 1
    /\ LET b == CHOOSE j \in B : TRUE IN
         c[Succ(b)] = Dec(c[b])

Fairness ==
  /\ SF_vars(SourceStep)
  /\ \A i \in Procs \ {Src} : WF_vars(Copy(i))

Spec == Init /\ [][Next]_vars /\ Fairness

SafetyInvariant == [] TypeOK

Stabilization == <>[] UniqueToken(cnt)

Circulation == []<>(SourceStep)

Liveness == Stabilization /\ Circulation

PROPERTY SafetyInvariant
PROPERTY Stabilization
PROPERTY Liveness

=============================================================================