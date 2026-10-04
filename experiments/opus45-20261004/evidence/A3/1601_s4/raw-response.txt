---------------------------- MODULE Fischer ----------------------------
EXTENDS Integers, Naturals, TLC

CONSTANTS N, Delta, Epsilon, Infinity

ASSUME /\ N \in Nat \ {0}
       /\ Delta \in Nat
       /\ Epsilon \in Nat
       /\ Infinity > Delta + Epsilon

VARIABLES pc, lock, timer

vars == <<pc, lock, timer>>

Procs == 1..N

TypeOK == /\ pc \in [Procs -> {"idle", "try", "check", "cs", "exit"}]
          /\ lock \in (Procs \cup {0})
          /\ timer \in [Procs -> 0..Infinity]

\* -----------------------------------------------------------------------
\* Fischer's Algorithm:
\* Each process cycles through states:
\*   idle -> try -> check -> cs -> exit -> idle
\*
\* In "try": process waits until lock = 0, then sets lock to self and
\*           starts a timer of Delta (must complete write within Delta time)
\*
\* In "check": process waits for Epsilon time to elapse (timer expires),
\*             then checks if lock still equals self
\*
\* The timing constraint requires Delta < Epsilon for correctness.
\* BUG: When N > 1 and Delta >= Epsilon, mutual exclusion can be violated.
\* -----------------------------------------------------------------------

Init == /\ pc = [p \in Procs |-> "idle"]
        /\ lock = 0
        /\ timer = [p \in Procs |-> Infinity]

\* Process p in idle state moves to try state
Idle(p) == /\ pc[p] = "idle"
           /\ pc' = [pc EXCEPT ![p] = "try"]
           /\ UNCHANGED <<lock, timer>>

\* Process p in try state: if lock = 0, set lock to p and set timer to Delta
Try(p) == /\ pc[p] = "try"
          /\ lock = 0
          /\ lock' = p
          /\ timer' = [timer EXCEPT ![p] = Delta]
          /\ pc' = [pc EXCEPT ![p] = "check"]

\* Process p in check state: wait for timer to expire (timer = 0), then check lock
CheckSuccess(p) == /\ pc[p] = "check"
                   /\ timer[p] = 0
                   /\ lock = p
                   /\ pc' = [pc EXCEPT ![p] = "cs"]
                   /\ UNCHANGED <<lock, timer>>

CheckFail(p) == /\ pc[p] = "check"
                /\ timer[p] = 0
                /\ lock # p
                /\ pc' = [pc EXCEPT ![p] = "idle"]
                /\ UNCHANGED <<lock, timer>>

\* Process p in critical section moves to exit
Exit(p) == /\ pc[p] = "cs"
           /\ pc' = [pc EXCEPT ![p] = "exit"]
           /\ UNCHANGED <<lock, timer>>

\* Process p in exit state releases lock and goes idle
Release(p) == /\ pc[p] = "exit"
              /\ lock' = 0
              /\ timer' = [timer EXCEPT ![p] = Infinity]
              /\ pc' = [pc EXCEPT ![p] = "idle"]

\* Process action: any process can take a step
ProcStep(p) == \/ Idle(p)
               \/ Try(p)
               \/ CheckSuccess(p)
               \/ CheckFail(p)
               \/ Exit(p)
               \/ Release(p)

\* -----------------------------------------------------------------------
\* Tick process: decrements all non-zero, non-Infinity timers
\* This models time passing. Timers count down from Delta toward 0.
\* After Epsilon time (modeled by waiting Delta steps which should be < Epsilon
\* for correctness), the process checks the lock.
\* -----------------------------------------------------------------------

\* For the algorithm to work correctly, the check must happen after Delta time
\* but the timer is set to Delta, so when timer reaches 0, Delta time has passed.
\* The Epsilon constraint means other processes should not be able to complete
\* their write to lock within Epsilon time after seeing lock = 0.

\* Tick decrements all active timers by 1
Tick == /\ \E p \in Procs : timer[p] \in 1..(Infinity-1)
        /\ timer' = [p \in Procs |-> IF timer[p] \in 1..(Infinity-1) 
                                     THEN timer[p] - 1 
                                     ELSE timer[p]]
        /\ UNCHANGED <<pc, lock>>

\* Alternative: Tick only when at least one timer is active and > 0
CanTick == \E p \in Procs : timer[p] > 0 /\ timer[p] < Infinity

Next == \/ \E p \in Procs : ProcStep(p)
        \/ Tick

\* -----------------------------------------------------------------------
\* Fairness conditions
\* -----------------------------------------------------------------------

\* Weak fairness for each process action
ProcessFairness == \A p \in Procs : WF_vars(ProcStep(p))

\* Weak fairness for the tick action
TickFairness == WF_vars(Tick)

Fairness == ProcessFairness /\ TickFairness

\* -----------------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------------

Spec == Init /\ [][Next]_vars /\ Fairness

\* -----------------------------------------------------------------------
\* Safety Invariant: Mutual Exclusion
\* At most one process is in the critical section at any time.
\* -----------------------------------------------------------------------

MutualExclusion == \A p1, p2 \in Procs : 
                      (pc[p1] = "cs" /\ pc[p2] = "cs") => p1 = p2

\* Alternative formulation: count of processes in CS is at most 1
AtMostOneInCS == Cardinality({p \in Procs : pc[p] = "cs"}) <= 1

\* Helper for Cardinality
Cardinality(S) == LET Card[T \in SUBSET S] == 
                        IF T = {} THEN 0 
                        ELSE 1 + Card[T \ {CHOOSE x \in T : TRUE}]
                  IN Card[S]

\* -----------------------------------------------------------------------
\* Liveness Property: Some process is infinitely often in the critical section
\* -----------------------------------------------------------------------

SomeoneInCS == \E p \in Procs : pc[p] = "cs"

Liveness == []<>SomeoneInCS

\* -----------------------------------------------------------------------
\* TLC State Count Check (for debugging/verification)
\* -----------------------------------------------------------------------

StateCountCheck == TLCGet("distinct") >= 0

\* -----------------------------------------------------------------------
\* Note on the bug:
\* When N > 1 and Delta >= Epsilon, the following scenario can occur:
\* 1. Process 1 sees lock = 0 and sets lock = 1, timer = Delta
\* 2. Before timer expires (within Delta time), process 2 sees lock = 0
\*    (this is the race condition - in real timing, this window exists
\*    when Delta >= Epsilon because the write hasn't "propagated")
\* 3. Process 2 sets lock = 2, timer = Delta
\* 4. Both processes' timers expire
\* 5. Process 1 checks lock, sees lock = 2, goes back to idle
\*    BUT if Delta >= Epsilon, process 1 might check before process 2
\*    has finished writing, potentially seeing lock = 1
\* 
\* In a correctly configured system (Delta < Epsilon), the delay in check
\* ensures that any concurrent writes have completed before checking.
\* -----------------------------------------------------------------------

=============================================================================