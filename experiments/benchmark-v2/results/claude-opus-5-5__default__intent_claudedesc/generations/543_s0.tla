---------------------------- MODULE ConcurrentCounter ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N   \* number of processes (e.g., 5)

ASSUME N \in Nat /\ N >= 1

Procs  == 1..N
Uninit == -1          \* value of a local variable that has not been initialized

VARIABLES
    x,      \* shared counter
    tmp,    \* tmp[p] : local temporary of process p
    lock,   \* TRUE iff the mutex is held
    pc      \* program counter of each process

vars == << x, tmp, lock, pc >>

-----------------------------------------------------------------------------
Init ==
    /\ x    = 0
    /\ tmp  = [p \in Procs |-> Uninit]
    /\ lock = FALSE
    /\ pc   = [p \in Procs |-> "Acquire"]

\* Acquire the mutex before entering the critical section
Acquire(p) ==
    /\ pc[p] = "Acquire"
    /\ lock = FALSE
    /\ lock' = TRUE
    /\ pc' = [pc EXCEPT ![p] = "Read"]
    /\ UNCHANGED << x, tmp >>

\* Critical section, step 1: read the shared counter into the local variable
Read(p) ==
    /\ pc[p] = "Read"
    /\ tmp' = [tmp EXCEPT ![p] = x]
    /\ pc' = [pc EXCEPT ![p] = "Write"]
    /\ UNCHANGED << x, lock >>

\* Critical section, step 2: write back the incremented value and release the mutex
Write(p) ==
    /\ pc[p] = "Write"
    /\ x' = tmp[p] + 1
    /\ lock' = FALSE
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED tmp

Proc(p) == Acquire(p) \/ Read(p) \/ Write(p)

\* Stuttering step once every process has finished
Terminating ==
    /\ \A p \in Procs : pc[p] = "Done"
    /\ UNCHANGED vars

Next == (\E p \in Procs : Proc(p)) \/ Terminating

Fairness == \A p \in Procs : WF_vars(Proc(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

TypeOK ==
    /\ x \in 0..N
    /\ tmp \in [Procs -> (0..N) \cup {Uninit}]
    /\ lock \in BOOLEAN
    /\ pc \in [Procs -> {"Acquire", "Read", "Write", "Done"}]

InCS(p) == pc[p] \in {"Read", "Write"}

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(InCS(p) /\ InCS(q))

AllDone == \A p \in Procs : pc[p] = "Done"

Correctness == AllDone => (x = N)

\* Liveness properties

Termination == <>AllDone

EventuallyCorrect == <>(x = N)

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ MutualExclusion /\ Correctness)
THEOREM Spec => Termination
=============================================================================