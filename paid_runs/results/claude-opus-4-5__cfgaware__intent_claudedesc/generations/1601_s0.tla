---------------------------- MODULE Fischer ----------------------------

EXTENDS Naturals, Sequences

CONSTANTS N, Epsilon, Delta

VARIABLES lock, pc, timer

vars == <<lock, pc, timer>>

Procs == 1..N

\* Process states:
\* "idle" - not trying to enter critical section
\* "wait" - waiting for lock to be 0
\* "set" - has set lock to its id, waiting for delta timer
\* "check" - checking if lock still holds its id after epsilon timer
\* "cs" - in critical section

TypeOK ==
    /\ lock \in 0..N
    /\ pc \in [Procs -> {"idle", "wait", "set", "check", "cs"}]
    /\ timer \in [Procs -> 0..Max(Delta, Epsilon) + 1]

Max(a, b) == IF a > b THEN a ELSE b

Init ==
    /\ lock = 0
    /\ pc = [p \in Procs |-> "idle"]
    /\ timer = [p \in Procs |-> 0]

\* Process p starts trying to enter critical section
Start(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ timer' = timer
    /\ lock' = lock

\* Process p waits until lock is 0, then sets timer to Delta and writes its id
SetLock(p) ==
    /\ pc[p] = "wait"
    /\ lock = 0
    /\ lock' = p
    /\ timer' = [timer EXCEPT ![p] = Delta]
    /\ pc' = [pc EXCEPT ![p] = "set"]

\* Process p's delta timer expired, now set epsilon timer and go to check
StartCheck(p) ==
    /\ pc[p] = "set"
    /\ timer[p] = 0
    /\ timer' = [timer EXCEPT ![p] = Epsilon]
    /\ pc' = [pc EXCEPT ![p] = "check"]
    /\ lock' = lock

\* Process p's epsilon timer expired, check if lock still holds its id
CheckLock(p) ==
    /\ pc[p] = "check"
    /\ timer[p] = 0
    /\ IF lock = p
       THEN pc' = [pc EXCEPT ![p] = "cs"]
       ELSE pc' = [pc EXCEPT ![p] = "idle"]
    /\ timer' = timer
    /\ lock' = lock

\* Process p exits critical section
Exit(p) ==
    /\ pc[p] = "cs"
    /\ lock' = 0
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ timer' = timer

\* Clock decrements all active timers when all are positive
\* Only decrements timers for processes that are in "set" or "check" state
ActiveProcs == {p \in Procs : pc[p] \in {"set", "check"}}

AllTimersPositive ==
    \A p \in ActiveProcs : timer[p] > 0

Tick ==
    /\ ActiveProcs /= {}
    /\ AllTimersPositive
    /\ timer' = [p \in Procs |-> IF p \in ActiveProcs THEN timer[p] - 1 ELSE timer[p]]
    /\ pc' = pc
    /\ lock' = lock

\* Process actions
ProcessAction(p) ==
    \/ Start(p)
    \/ SetLock(p)
    \/ StartCheck(p)
    \/ CheckLock(p)
    \/ Exit(p)

Next ==
    \/ \E p \in Procs : ProcessAction(p)
    \/ Tick

\* Fairness conditions
ProcessFairness == \A p \in Procs : WF_vars(ProcessAction(p))
ClockFairness == WF_vars(Tick)

Fairness == ProcessFairness /\ ClockFairness

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Mutual exclusion - no two processes in critical section
Invariant ==
    \A p, q \in Procs : (pc[p] = "cs" /\ pc[q] = "cs") => p = q

\* Liveness: Some process enters the critical section infinitely often
InCS == \E p \in Procs : pc[p] = "cs"
Liveness == []<>InCS

=============================================================================