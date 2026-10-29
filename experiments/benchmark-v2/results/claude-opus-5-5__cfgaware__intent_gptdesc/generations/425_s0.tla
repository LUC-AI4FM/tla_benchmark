---- MODULE CountdownToCutoff ----
EXTENDS Integers

\* Fixed starting value (negative) and fixed cutoff (below the start).
StartVal == -3
Cutoff   == -10

VARIABLE x

vars == << x >>

TypeOK == x \in Int

Init == x = StartVal

Decrement ==
    /\ x > Cutoff
    /\ x' = x - 1

Stay ==
    /\ x = Cutoff
    /\ x' = x

Next == Decrement \/ Stay

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety invariants
Inv ==
    /\ TypeOK
    /\ x <= StartVal
    /\ x >= Cutoff

\* Action properties: the variable never increases, and once it reaches
\* the cutoff it stays there.
NeverIncreases == [][x' <= x]_vars

StaysAtCutoff == [][x = Cutoff => x' = Cutoff]_vars

\* Once the cutoff is reached, it holds forever.
CutoffStable == [](x = Cutoff => [](x = Cutoff))

\* Liveness: the system eventually reaches the cutoff and stays there.
EventuallyCutoff == <>(x = Cutoff)

EventuallyAlwaysCutoff == <>[](x = Cutoff)

====