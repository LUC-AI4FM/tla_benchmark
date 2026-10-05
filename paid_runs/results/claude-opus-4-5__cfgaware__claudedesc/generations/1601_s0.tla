---------------------------- MODULE Fischer ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, Delta, Epsilon

VARIABLES x, timer, pc

vars == <<x, timer, pc>>

Procs == 1..N

Init ==
    /\ x = 0
    /\ timer = [i \in 0..N |-> 0]
    /\ pc = [i \in 0..N |-> IF i = 0 THEN "tick" ELSE "a"]

\* Process actions for processes 1..N

\* Label a: start of loop, go to b
a(self) ==
    /\ self \in Procs
    /\ pc[self] = "a"
    /\ pc' = [pc EXCEPT ![self] = "b"]
    /\ UNCHANGED <<x, timer>>

\* Label b: check if x = self, if so go to cs, else go to c
b(self) ==
    /\ self \in Procs
    /\ pc[self] = "b"
    /\ IF x = self
       THEN pc' = [pc EXCEPT ![self] = "cs"]
       ELSE pc' = [pc EXCEPT ![self] = "c"]
    /\ UNCHANGED <<x, timer>>

\* Label c: wait until x = 0
c(self) ==
    /\ self \in Procs
    /\ pc[self] = "c"
    /\ x = 0
    /\ pc' = [pc EXCEPT ![self] = "d"]
    /\ UNCHANGED <<x, timer>>

\* Label d: set timer to Delta and write self into x
d(self) ==
    /\ self \in Procs
    /\ pc[self] = "d"
    /\ timer' = [timer EXCEPT ![self] = Delta]
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "e"]

\* Label e: set timer to Epsilon and wait until timer expires (timer = 0)
e(self) ==
    /\ self \in Procs
    /\ pc[self] = "e"
    /\ timer[self] = 0
    /\ timer' = [timer EXCEPT ![self] = Epsilon]
    /\ pc' = [pc EXCEPT ![self] = "wait"]
    /\ UNCHANGED x

\* wait: wait for timer to reach 0 after setting Epsilon
wait(self) ==
    /\ self \in Procs
    /\ pc[self] = "wait"
    /\ timer[self] = 0
    /\ pc' = [pc EXCEPT ![self] = "b"]
    /\ UNCHANGED <<x, timer>>

\* Label cs: critical section
cs(self) ==
    /\ self \in Procs
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "f"]
    /\ UNCHANGED <<x, timer>>

\* Label f: exit critical section, reset x to 0, go back to a
f(self) ==
    /\ self \in Procs
    /\ pc[self] = "f"
    /\ x' = 0
    /\ pc' = [pc EXCEPT ![self] = "a"]
    /\ UNCHANGED timer

\* Tick process (process 0): decrements all finite timers by one
\* Only when every timer is strictly positive
AllTimersPositive ==
    \A i \in 0..N : timer[i] > 0

Tick ==
    /\ pc[0] = "tick"
    /\ AllTimersPositive
    /\ timer' = [i \in 0..N |-> timer[i] - 1]
    /\ UNCHANGED <<x, pc>>

\* Next state relation
proc(self) ==
    \/ a(self)
    \/ b(self)
    \/ c(self)
    \/ d(self)
    \/ e(self)
    \/ wait(self)
    \/ cs(self)
    \/ f(self)

Next ==
    \/ Tick
    \/ \E self \in Procs : proc(self)

\* Fairness conditions
Fairness ==
    /\ WF_vars(Tick)
    /\ \A self \in Procs : WF_vars(proc(self))

\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* Invariant: Mutual exclusion - no two distinct processes in critical section
SomeInCS == {i \in Procs : pc[i] = "cs"}

Invariant == Cardinality(SomeInCS) <= 1

\* Liveness: Some process is in the critical section infinitely often
ClaimLock == \E i \in Procs : pc[i] = "cs"

Liveness == []<>ClaimLock

=============================================================================