---------------------------- MODULE FastMutex ----------------------------
\* Peterson's N-process tournament algorithm adapted as a fast mutex
\* with bounded waiting, ensuring mutual exclusion, deadlock freedom,
\* and starvation freedom under weak fairness.

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

\* Number of levels in the tournament tree (ceiling of log2(N))
\* For N processes, we need enough levels to form a binary tournament
Levels == 1..N

VARIABLES
    pc,         \* Program counter for each process
    level,      \* level[p] = current level process p is competing at (0 = not competing)
    last,       \* last[lv] = last process to enter level lv (used for tie-breaking)
    waiting     \* waiting[p] = TRUE if process p is in a waiting/spinning state

vars == <<pc, level, last, waiting>>

\* Program counter states:
\* "noncritical" - in noncritical section
\* "try"         - starting to try to enter CS, will set level
\* "check"       - checking if can proceed to next level
\* "wait"        - waiting/spinning for condition
\* "critical"    - in critical section
\* "exit"        - exiting critical section

TypeOK ==
    /\ pc \in [Procs -> {"noncritical", "try", "check", "wait", "critical", "exit"}]
    /\ level \in [Procs -> 0..N]
    /\ last \in [Levels -> 0..N]
    /\ waiting \in [Procs -> BOOLEAN]

Init ==
    /\ pc = [p \in Procs |-> "noncritical"]
    /\ level = [p \in Procs |-> 0]
    /\ last = [lv \in Levels |-> 0]
    /\ waiting = [p \in Procs |-> FALSE]

\* Process p starts trying to enter critical section
TryEnter(p) ==
    /\ pc[p] = "noncritical"
    /\ pc' = [pc EXCEPT ![p] = "try"]
    /\ level' = [level EXCEPT ![p] = 1]
    /\ last' = [last EXCEPT ![1] = p]
    /\ waiting' = [waiting EXCEPT ![p] = FALSE]

\* Process p checks if it can proceed at current level
Check(p) ==
    /\ pc[p] = "try"
    /\ pc' = [pc EXCEPT ![p] = "check"]
    /\ UNCHANGED <<level, last, waiting>>

\* At level lv, process p can proceed if:
\* - It's not the last one to arrive at this level, OR
\* - No other process is at this level or higher
CanProceed(p, lv) ==
    \/ last[lv] # p
    \/ ~\E q \in Procs : q # p /\ level[q] >= lv

\* Process p decides whether to wait or proceed
DecideWait(p) ==
    /\ pc[p] = "check"
    /\ LET lv == level[p]
       IN IF CanProceed(p, lv)
          THEN \* Can proceed to next level or enter CS
               IF lv >= N - 1
               THEN \* Reached top level, enter critical section
                    /\ pc' = [pc EXCEPT ![p] = "critical"]
                    /\ UNCHANGED <<level, last, waiting>>
               ELSE \* Move to next level
                    /\ level' = [level EXCEPT ![p] = lv + 1]
                    /\ last' = [last EXCEPT ![lv + 1] = p]
                    /\ pc' = [pc EXCEPT ![p] = "try"]
                    /\ UNCHANGED waiting
          ELSE \* Must wait
               /\ pc' = [pc EXCEPT ![p] = "wait"]
               /\ waiting' = [waiting EXCEPT ![p] = TRUE]
               /\ UNCHANGED <<level, last>>

\* Process p is waiting and rechecks condition
Waiting(p) ==
    /\ pc[p] = "wait"
    /\ LET lv == level[p]
       IN IF CanProceed(p, lv)
          THEN \* Condition now satisfied
               /\ waiting' = [waiting EXCEPT ![p] = FALSE]
               /\ IF lv >= N - 1
                  THEN /\ pc' = [pc EXCEPT ![p] = "critical"]
                       /\ UNCHANGED <<level, last>>
                  ELSE /\ level' = [level EXCEPT ![p] = lv + 1]
                       /\ last' = [last EXCEPT ![lv + 1] = p]
                       /\ pc' = [pc EXCEPT ![p] = "try"]
          ELSE \* Keep waiting
               /\ UNCHANGED vars

\* Process p exits critical section
Exit(p) ==
    /\ pc[p] = "critical"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<level, last, waiting>>

\* Process p completes exit and returns to noncritical section
CompleteExit(p) ==
    /\ pc[p] = "exit"
    /\ level' = [level EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "noncritical"]
    /\ UNCHANGED <<last, waiting>>

\* All possible actions for process p
ProcessAction(p) ==
    \/ TryEnter(p)
    \/ Check(p)
    \/ DecideWait(p)
    \/ Waiting(p)
    \/ Exit(p)
    \/ CompleteExit(p)

Next == \E p \in Procs : ProcessAction(p)

\* ----- SAFETY PROPERTIES -----

\* Mutual exclusion: at most one process in critical section
MutualExclusion ==
    Cardinality({p \in Procs : pc[p] = "critical"}) <= 1

\* ----- LIVENESS PROPERTIES -----

\* Some process is trying to enter (not in noncritical section)
SomeoneTrying ==
    \E p \in Procs : pc[p] # "noncritical"

\* Some process is in critical section
SomeoneInCS ==
    \E p \in Procs : pc[p] = "critical"

\* Deadlock freedom: if someone is trying, eventually someone enters CS
DeadlockFreedom ==
    SomeoneTrying ~> SomeoneInCS

\* Process p is trying to enter
Trying(p) == pc[p] \in {"try", "check", "wait"}

\* Process p is in critical section
InCS(p) == pc[p] = "critical"

\* Starvation freedom: every process that tries eventually enters
StarvationFreedom ==
    \A p \in Procs : Trying(p) ~> InCS(p)

\* ----- FAIRNESS CONDITIONS -----

\* Weak fairness for non-blocking progress steps
\* We need fairness on steps that make progress when enabled
FairProcess(p) ==
    /\ WF_vars(TryEnter(p))
    /\ WF_vars(Check(p))
    /\ WF_vars(DecideWait(p))
    /\ WF_vars(Waiting(p))
    /\ WF_vars(Exit(p))
    /\ WF_vars(CompleteExit(p))

Fairness == \A p \in Procs : FairProcess(p)

\* ----- SPECIFICATION -----

Spec == Init /\ [][Next]_vars /\ Fairness

\* ----- THEOREMS TO CHECK -----

\* Safety invariant
SafetyInvariant == TypeOK /\ MutualExclusion

\* The specification should satisfy:
\* THEOREM Spec => []SafetyInvariant
\* THEOREM Spec => DeadlockFreedom
\* THEOREM Spec => StarvationFreedom

==========================================================================