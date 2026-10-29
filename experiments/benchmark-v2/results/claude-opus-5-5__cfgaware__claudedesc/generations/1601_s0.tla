---- MODULE Fischer ----
EXTENDS Naturals, TLC

CONSTANTS N, Delta, Epsilon

ASSUME /\ N \in Nat \ {0}
       /\ Delta \in Nat
       /\ Epsilon \in Nat

Infinity == Delta + Epsilon + 1

Proc == 1..N

VARIABLES x, timer, pc

vars == << x, timer, pc >>

Init == /\ x = 0
        /\ timer = [i \in Proc |-> Infinity]
        /\ pc = [i \in Proc |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ pc' = [pc EXCEPT ![self] = "c"]
           /\ UNCHANGED << x, timer >>

c(self) == /\ pc[self] = "c"
           /\ x = 0
           /\ timer' = [timer EXCEPT ![self] = Delta]
           /\ pc' = [pc EXCEPT ![self] = "d"]
           /\ x' = x

d(self) == /\ pc[self] = "d"
           /\ x' = self
           /\ timer' = [timer EXCEPT ![self] = Epsilon]
           /\ pc' = [pc EXCEPT ![self] = "e"]

e(self) == /\ pc[self] = "e"
           /\ timer[self] = 0
           /\ timer' = [timer EXCEPT ![self] = Infinity]
           /\ pc' = [pc EXCEPT ![self] = "b"]
           /\ x' = x

b(self) == /\ pc[self] = "b"
           /\ IF x = self
                 THEN pc' = [pc EXCEPT ![self] = "cs"]
                 ELSE pc' = [pc EXCEPT ![self] = "c"]
           /\ UNCHANGED << x, timer >>

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "f"]
            /\ UNCHANGED << x, timer >>

f(self) == /\ pc[self] = "f"
           /\ x' = 0
           /\ pc' = [pc EXCEPT ![self] = "a"]
           /\ timer' = timer

P(self) == a(self) \/ c(self) \/ d(self) \/ e(self)
           \/ b(self) \/ cs(self) \/ f(self)

Tick == /\ \A i \in Proc : timer[i] > 0
        /\ timer' = [i \in Proc |->
                       IF timer[i] = Infinity THEN Infinity
                                              ELSE timer[i] - 1]
        /\ UNCHANGED << x, pc >>

Next == Tick \/ (\E self \in Proc : P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Tick)
        /\ \A self \in Proc : WF_vars(P(self))

TypeOK == /\ x \in 0..N
          /\ timer \in [Proc -> 0..Infinity]
          /\ pc \in [Proc -> {"a", "b", "c", "d", "e", "cs", "f"}]

Invariant == \A i, j \in Proc : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

SomeInCS == \E i \in Proc : pc[i] = "cs"

Liveness == []<>SomeInCS

ClaimLock == \E i \in Proc : pc[i] = "e" /\ x = i

\* Possibility checking: count reachable states satisfying each predicate.
\* Register 1 counts SomeInCS states, register 2 counts ClaimLock states.
Bump(r, Pred) ==
    TLCSet(r, (IF TLCGet("level") <= 1 THEN 0 ELSE TLCGet(r))
              + (IF Pred THEN 1 ELSE 0))

_POSSIBLE == /\ Bump(1, SomeInCS)
             /\ Bump(2, ClaimLock)

PossibleCounts ==
    IF Delta < Epsilon
       THEN /\ TLCGet(1) > 0
            /\ TLCGet(2) > 0
       ELSE PrintT("Violation expected: Delta >= Epsilon")
====