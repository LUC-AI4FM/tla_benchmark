---------------------------- MODULE Fischer ----------------------------
\* Fischer's timed mutual exclusion protocol for N symmetric processes
\* Processes coordinate using a single shared memory location and local timers

EXTENDS Integers, Naturals

CONSTANTS 
    N,          \* Number of processes (processes are 1..N)
    Delta1,     \* Long delay (time to wait before reading lock)
    Delta2,     \* Short delay (time window to write lock)
    INF         \* Sentinel value representing "infinite" / disabled timer

ASSUME N \in Nat /\ N >= 1
ASSUME Delta1 \in Nat /\ Delta2 \in Nat
ASSUME Delta1 >= Delta2  \* Fischer's requirement: long delay >= short delay
ASSUME INF > Delta1 /\ INF > Delta2  \* INF must be larger than any finite delay

Procs == 1..N  \* Process identifiers

VARIABLES
    pc,     \* Program counter for each process: "idle", "wait", "set", "check", "cs", "exit"
    lock,   \* Shared memory location: 0 means empty, i means process i holds reservation
    timer   \* Local timer for each process: INF means disabled, 0..Delta1 means active countdown

vars == <<pc, lock, timer>>

\* Type invariant
TypeOK ==
    /\ pc \in [Procs -> {"idle", "wait", "set", "check", "cs", "exit"}]
    /\ lock \in 0..N
    /\ timer \in [Procs -> 0..INF]

\* Initial state: all processes idle, lock free, timers disabled
Init ==
    /\ pc = [i \in Procs |-> "idle"]
    /\ lock = 0
    /\ timer = [i \in Procs |-> INF]

\* Process i starts trying to enter critical section
\* From idle, move to wait state
Start(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ UNCHANGED <<lock, timer>>

\* Process i waits until lock is empty (lock = 0)
\* When lock is 0, move to set state and start timer for Delta2 (short delay)
Wait(i) ==
    /\ pc[i] = "wait"
    /\ lock = 0
    /\ pc' = [pc EXCEPT ![i] = "set"]
    /\ timer' = [timer EXCEPT ![i] = Delta2]
    /\ UNCHANGED lock

\* Process i sets the lock to its id before timer expires
\* Must complete within Delta2 time units
Set(i) ==
    /\ pc[i] = "set"
    /\ timer[i] > 0  \* Still have time to set
    /\ lock' = i
    /\ pc' = [pc EXCEPT ![i] = "check"]
    /\ timer' = [timer EXCEPT ![i] = Delta1]  \* Set timer to Delta1 (long delay)

\* Process i checks if it still holds the lock after Delta1 delay
\* Timer must have expired (reached 0)
Check(i) ==
    /\ pc[i] = "check"
    /\ timer[i] = 0  \* Timer expired, Delta1 time has passed
    /\ IF lock = i
       THEN /\ pc' = [pc EXCEPT ![i] = "cs"]
            /\ timer' = [timer EXCEPT ![i] = INF]
       ELSE /\ pc' = [pc EXCEPT ![i] = "wait"]
            /\ timer' = [timer EXCEPT ![i] = INF]
    /\ UNCHANGED lock

\* Process i is in critical section, moves to exit
Exit(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED <<lock, timer>>

\* Process i exits critical section, clears lock
Release(i) ==
    /\ pc[i] = "exit"
    /\ lock' = 0
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ timer' = [timer EXCEPT ![i] = INF]

\* Combined process step for process i
Proc(i) ==
    \/ Start(i)
    \/ Wait(i)
    \/ Set(i)
    \/ Check(i)
    \/ Exit(i)
    \/ Release(i)

\* Decrement active timers (timers that are not INF and not already 0)
DecrementTimer(t) ==
    IF t = INF THEN INF
    ELSE IF t > 0 THEN t - 1
    ELSE 0

\* Global tick: advances all timers synchronously
\* Only tick when there's at least one active timer to prevent infinite ticking
Tick ==
    /\ \E i \in Procs : timer[i] /= INF /\ timer[i] > 0
    /\ timer' = [i \in Procs |-> DecrementTimer(timer[i])]
    /\ UNCHANGED <<pc, lock>>

\* Next state relation
Next ==
    \/ \E i \in Procs : Proc(i)
    \/ Tick

\* Fairness conditions
\* Strong fairness for each process's entry attempts
\* Weak fairness for tick to ensure timers advance
Fairness ==
    /\ \A i \in Procs : SF_vars(Proc(i))
    /\ WF_vars(Tick)

\* Complete specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* --------------------------------------------------------------------------
\* SAFETY PROPERTIES
\* --------------------------------------------------------------------------

\* Mutual exclusion: at most one process in critical section
MutualExclusion ==
    \A i, j \in Procs : (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Invariant: mutual exclusion must always hold
Inv_MutualExclusion == MutualExclusion

\* --------------------------------------------------------------------------
\* LIVENESS PROPERTIES
\* --------------------------------------------------------------------------

\* Every process that starts trying will eventually enter the critical section
\* (requires fairness)
Liveness_Entry ==
    \A i \in Procs : (pc[i] = "wait") ~> (pc[i] = "cs")

\* Every process that enters CS will eventually exit
Liveness_Exit ==
    \A i \in Procs : (pc[i] = "cs") ~> (pc[i] = "idle")

\* Combined progress property
Progress ==
    \A i \in Procs : (pc[i] /= "idle") ~> (pc[i] = "cs")

\* --------------------------------------------------------------------------
\* TEMPORAL PROPERTIES FOR WITNESSING POTENTIAL VIOLATIONS
\* --------------------------------------------------------------------------

\* Property to check: it should NEVER be possible for two processes to be in CS
\* If this is violated, we have a mutual exclusion failure
\* Use: check that ~TwoInCS is always true (should pass)
TwoInCS ==
    \E i, j \in Procs : i /= j /\ pc[i] = "cs" /\ pc[j] = "cs"

\* Check this property - should be invariant
NoTwoInCS == ~TwoInCS

\* Property: a process has claimed the lock but might not get CS
\* This represents the "set lock but may fail check" scenario
\* This state can exist (not a violation, just a witness)
ClaimedButMayFail ==
    \E i \in Procs : 
        /\ pc[i] = "check"
        /\ lock = i
        /\ timer[i] > 0

\* Property: witness existence of state where process claimed lock but 
\* another process could steal it (shows the protocol's timing sensitivity)
LockStealPossible ==
    \E i, j \in Procs :
        /\ i /= j
        /\ lock = i
        /\ pc[i] = "check"
        /\ timer[i] > 0
        /\ pc[j] = "set"
        /\ timer[j] > 0

\* Negation for model checking - this SHOULD be reachable in some traces
\* (checking ~[]~LockStealPossible would show it's possible)
NeverLockSteal == []~LockStealPossible

\* --------------------------------------------------------------------------
\* HELPER PREDICATES
\* --------------------------------------------------------------------------

\* Number of processes in critical section
NumInCS == Cardinality({i \in Procs : pc[i] = "cs"})

\* At most one in CS (alternative formulation)
AtMostOneInCS == NumInCS <= 1

\* Some process is trying to enter
SomeTrying == \E i \in Procs : pc[i] \in {"wait", "set", "check"}

\* Some process is in critical section
SomeInCS == \E i \in Procs : pc[i] = "cs"

\* Cardinality helper (for NumInCS)
Cardinality(S) == 
    LET Card[T \in SUBSET S] ==
        IF T = {} THEN 0
        ELSE 1 + Card[T \ {CHOOSE x \in T : TRUE}]
    IN Card[S]

==========================================================================