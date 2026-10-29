---------------------------- MODULE Fischer ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, Delta, Epsilon

ASSUME /\ N \in Nat \ {0}
       /\ Delta \in Nat
       /\ Epsilon \in Nat

Proc == 1..N

\* A value larger than any real timer setting; it marks a timer that is not running.
Infinity == Delta + Epsilon + 1

VARIABLES x, timer, pc

vars == <<x, timer, pc>>

TypeOK ==
  /\ x \in 0..N
  /\ timer \in [Proc -> 0..Infinity]
  /\ pc \in [Proc -> {"a", "b", "c", "cs", "d"}]

Init ==
  /\ x = 0
  /\ timer = [p \in Proc |-> Infinity]
  /\ pc = [p \in Proc |-> "a"]

\* Wait until the lock is free, then start a timer of length Delta.
a(self) ==
  /\ pc[self] = "a"
  /\ x = 0
  /\ timer' = [timer EXCEPT ![self] = Delta]
  /\ pc' = [pc EXCEPT ![self] = "b"]
  /\ UNCHANGED x

\* Write own id into the lock and start a timer of length Epsilon.
b(self) ==
  /\ pc[self] = "b"
  /\ x' = self
  /\ timer' = [timer EXCEPT ![self] = Epsilon]
  /\ pc' = [pc EXCEPT ![self] = "c"]

\* Wait for the timer to expire, then check whether the lock still holds own id.
c(self) ==
  /\ pc[self] = "c"
  /\ timer[self] = 0
  /\ timer' = [timer EXCEPT ![self] = Infinity]
  /\ IF x # self
       THEN pc' = [pc EXCEPT ![self] = "a"]
       ELSE pc' = [pc EXCEPT ![self] = "cs"]
  /\ UNCHANGED x

\* Critical section.
cs(self) ==
  /\ pc[self] = "cs"
  /\ pc' = [pc EXCEPT ![self] = "d"]
  /\ UNCHANGED <<x, timer>>

\* Release the lock.
d(self) ==
  /\ pc[self] = "d"
  /\ x' = 0
  /\ pc' = [pc EXCEPT ![self] = "a"]
  /\ UNCHANGED timer

P(self) == a(self) \/ b(self) \/ c(self) \/ cs(self) \/ d(self)

\* The global clock ticks only when every timer is strictly positive.
Tick ==
  /\ \A p \in Proc : timer[p] > 0
  /\ timer' = [p \in Proc |-> IF timer[p] = Infinity
                                THEN Infinity
                                ELSE timer[p] - 1]
  /\ UNCHANGED <<x, pc>>

Next == Tick \/ (\E self \in Proc : P(self))

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A self \in Proc : WF_vars(P(self))
  /\ WF_vars(Tick)

-----------------------------------------------------------------------------
InCS(p) == pc[p] = "cs"

SomeInCS == \E p \in Proc : InCS(p)

ClaimLock == \E p \in Proc : pc[p] = "c" /\ x = p

PossibleCounts == Cardinality({p \in Proc : InCS(p)}) \in 0..N

\* Mutual exclusion
Invariant == \A p, q \in Proc : (p # q) => ~(InCS(p) /\ InCS(q))

\* Some process enters the critical section infinitely often
Liveness == []<>SomeInCS

_POSSIBLE == <>ClaimLock /\ <>SomeInCS
=============================================================================