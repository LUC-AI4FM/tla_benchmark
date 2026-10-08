---------------------------- MODULE Fischer ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, Delta, Epsilon

ASSUME N \in Nat /\ N >= 1
ASSUME Delta \in Nat /\ Delta >= 0
ASSUME Epsilon \in Nat /\ Epsilon >= 0

Procs == 1..N

VARIABLES
    pc,      \* program counter for each process: "idle", "wait", "set", "check", "cs"
    lock,    \* shared variable, 0 means free, otherwise holds process id
    timer    \* timer for each process, 0 means expired/inactive

vars == <<pc, lock, timer>>

TypeOK ==
    /\ pc \in [Procs -> {"idle", "wait", "set", "check", "cs"}]
    /\ lock \in 0..N
    /\ timer \in [Procs -> 0..Max(Delta, Epsilon) + 1]

Max(a, b) == IF a >= b THEN a ELSE b

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ lock = 0
    /\ timer = [p \in Procs |-> 0]

\* Process p starts attempting to enter CS, waits for lock to be 0
StartWait(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED <<lock, timer>>

\* Process p observes lock = 0 and moves to set phase with timer Delta
ObserveFree(p) ==
    /\ pc[p] = "wait"
    /\ lock = 0
    /\ pc' = [pc EXCEPT ![p] = "set"]
    /\ timer' = [timer EXCEPT ![p] = Delta]
    /\ UNCHANGED lock

\* Process p's timer expired, it writes its id to lock and starts check phase with timer Epsilon
SetLock(p) ==
    /\ pc[p] = "set"
    /\ timer[p] = 0
    /\ lock' = p
    /\ pc' = [pc EXCEPT ![p] = "check"]
    /\ timer' = [timer EXCEPT ![p] = Epsilon]

\* Process p's timer expired, it checks if lock still holds its id
CheckLock(p) ==
    /\ pc[p] = "check"
    /\ timer[p] = 0
    /\ IF lock = p
       THEN pc' = [pc EXCEPT ![p] = "cs"]
       ELSE pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<lock, timer>>

\* Process p exits the critical section
ExitCS(p) ==
    /\ pc[p] = "cs"
    /\ lock' = 0
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED timer

\* Process action: any process can take one of its enabled steps
ProcAction(p) ==
    \/ StartWait(p)
    \/ ObserveFree(p)
    \/ SetLock(p)
    \/ CheckLock(p)
    \/ ExitCS(p)

\* Clock tick: decrements all positive timers, but only when all timers are positive
\* This models synchronized time passage
AllTimersPositive ==
    \A p \in Procs : (pc[p] \in {"set", "check"}) => timer[p] > 0

SomeTimerActive ==
    \E p \in Procs : pc[p] \in {"set", "check"} /\ timer[p] > 0

Tick ==
    /\ SomeTimerActive
    /\ AllTimersPositive
    /\ timer' = [p \in Procs |-> IF pc[p] \in {"set", "check"} /\ timer[p] > 0 
                                  THEN timer[p] - 1 
                                  ELSE timer[p]]
    /\ UNCHANGED <<pc, lock>>

Next ==
    \/ \E p \in Procs : ProcAction(p)
    \/ Tick

\* Fairness: weak fairness for all process actions and clock
Fairness ==
    /\ \A p \in Procs : WF_vars(StartWait(p))
    /\ \A p \in Procs : WF_vars(ObserveFree(p))
    /\ \A p \in Procs : WF_vars(SetLock(p))
    /\ \A p \in Procs : WF_vars(CheckLock(p))
    /\ \A p \in Procs : WF_vars(ExitCS(p))
    /\ WF_vars(Tick)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Mutual Exclusion - no two distinct processes in CS simultaneously
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Liveness: Some process enters CS infinitely often
SomeoneInCS == \E p \in Procs : pc[p] = "cs"

Liveness == []<>SomeoneInCS

==========================================================================