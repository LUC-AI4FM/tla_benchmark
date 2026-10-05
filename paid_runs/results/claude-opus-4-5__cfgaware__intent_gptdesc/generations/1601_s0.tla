---------------------------- MODULE Fischer ----------------------------

EXTENDS Naturals, Sequences

CONSTANTS N, Epsilon, Delta, Inf

ASSUME N \in Nat /\ N > 0
ASSUME Epsilon \in Nat /\ Epsilon > 0
ASSUME Delta \in Nat /\ Delta > 0
ASSUME Delta >= Epsilon
ASSUME Inf \in Nat /\ Inf > Delta

VARIABLES lock, pc, timer

vars == <<lock, pc, timer>>

Procs == 1..N

TypeOK ==
    /\ lock \in {0} \cup Procs
    /\ pc \in [Procs -> {"idle", "wait", "set", "check", "cs", "exit"}]
    /\ timer \in [Procs -> 0..Inf]

Init ==
    /\ lock = 0
    /\ pc = [i \in Procs |-> "idle"]
    /\ timer = [i \in Procs |-> Inf]

\* Process i starts trying to enter the critical section
StartTrying(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ timer' = [timer EXCEPT ![i] = Inf]
    /\ UNCHANGED lock

\* Process i waits until lock is free
Wait(i) ==
    /\ pc[i] = "wait"
    /\ lock = 0
    /\ pc' = [pc EXCEPT ![i] = "set"]
    /\ UNCHANGED <<lock, timer>>

\* Process i sets the lock to its id and starts timer with Delta
SetLock(i) ==
    /\ pc[i] = "set"
    /\ lock' = i
    /\ timer' = [timer EXCEPT ![i] = Delta]
    /\ pc' = [pc EXCEPT ![i] = "check"]

\* Process i checks if it still holds the lock after waiting Epsilon time
Check(i) ==
    /\ pc[i] = "check"
    /\ timer[i] = 0
    /\ IF lock = i
       THEN pc' = [pc EXCEPT ![i] = "cs"]
       ELSE pc' = [pc EXCEPT ![i] = "wait"]
    /\ timer' = [timer EXCEPT ![i] = Inf]
    /\ UNCHANGED lock

\* Process i is in critical section and decides to exit
Exit(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED <<lock, timer>>

\* Process i releases the lock and returns to idle
Release(i) ==
    /\ pc[i] = "exit"
    /\ lock' = 0
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ timer' = [timer EXCEPT ![i] = Inf]

\* A process step for process i
ProcStep(i) ==
    \/ StartTrying(i)
    \/ Wait(i)
    \/ SetLock(i)
    \/ Check(i)
    \/ Exit(i)
    \/ Release(i)

\* Check if any process has an active timer that needs to tick
SomeTimerActive ==
    \E i \in Procs : timer[i] < Inf /\ timer[i] > 0

\* Global tick advances all active timers
Tick ==
    /\ SomeTimerActive
    /\ timer' = [i \in Procs |-> IF timer[i] < Inf /\ timer[i] > 0
                                 THEN timer[i] - 1
                                 ELSE timer[i]]
    /\ UNCHANGED <<lock, pc>>

\* Combined next state relation
Next ==
    \/ \E i \in Procs : ProcStep(i)
    \/ Tick

\* Fairness conditions
\* Strong fairness for each process's entry routine (all steps except Exit/Release)
ProcessFairness(i) ==
    /\ SF_vars(StartTrying(i))
    /\ SF_vars(Wait(i))
    /\ SF_vars(SetLock(i))
    /\ SF_vars(Check(i))
    /\ WF_vars(Exit(i))
    /\ WF_vars(Release(i))

\* Fair tick activity
TickFairness == WF_vars(Tick)

Fairness ==
    /\ \A i \in Procs : ProcessFairness(i)
    /\ TickFairness

\* The complete specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Mutual Exclusion
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* The invariant required by the configuration
Invariant == MutualExclusion

\* Count processes in critical section
InCS == {i \in Procs : pc[i] = "cs"}

\* Temporal property: No two processes ever in CS simultaneously
NeverTwoInCS == [](Cardinality(InCS) <= 1)

\* Define Cardinality for finite sets
RECURSIVE Cardinality(_)
Cardinality(S) ==
    IF S = {} THEN 0
    ELSE 1 + Cardinality(S \ {CHOOSE x \in S : TRUE})

\* Liveness: Every process that tries eventually enters CS
\* A process is trying if it's in wait, set, or check state
Trying(i) == pc[i] \in {"wait", "set", "check"}

\* Every process eventually enters the critical section if it keeps trying
EventualEntry(i) == [](Trying(i) => <>(pc[i] = "cs"))

\* Combined liveness property
Liveness == \A i \in Procs : EventualEntry(i)

\* Witness properties for potential violations (for model checking)
\* Exists a state where two are in CS (should be FALSE if MutualExclusion holds)
TwoInCS == \E i, j \in Procs : i # j /\ pc[i] = "cs" /\ pc[j] = "cs"

\* Exists a state where a process claimed lock but won't get CS
\* (process set the lock but another process will overwrite it)
ClaimedButLost(i) ==
    pc[i] = "check" /\ lock # i

SomeClaimedButLost == \E i \in Procs : ClaimedButLost(i)

=============================================================================