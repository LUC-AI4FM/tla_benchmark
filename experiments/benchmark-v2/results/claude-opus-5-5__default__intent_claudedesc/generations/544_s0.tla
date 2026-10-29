---------------------------- MODULE SemaphoreCounter ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

Procs == 1..N

VARIABLES
    counter,   \* shared counter
    sem,       \* binary semaphore: 1 = available, 0 = held
    tmp,       \* per-process local variable holding the value read
    pc         \* per-process program counter

vars == << counter, sem, tmp, pc >>

PCValues == {"acquire", "read", "write", "release", "Done"}

CS == {"read", "write", "release"}   \* critical section locations

TypeOK ==
    /\ counter \in Nat
    /\ sem \in {0, 1}
    /\ tmp \in [Procs -> Nat]
    /\ pc \in [Procs -> PCValues]

Init ==
    /\ counter = 0
    /\ sem = 1
    /\ tmp = [p \in Procs |-> 0]
    /\ pc = [p \in Procs |-> "acquire"]

\* Step 1: wait for and acquire the semaphore (blocking)
Acquire(p) ==
    /\ pc[p] = "acquire"
    /\ sem = 1
    /\ sem' = 0
    /\ pc' = [pc EXCEPT ![p] = "read"]
    /\ UNCHANGED << counter, tmp >>

\* Step 2: read the shared counter into a local variable
Read(p) ==
    /\ pc[p] = "read"
    /\ tmp' = [tmp EXCEPT ![p] = counter]
    /\ pc' = [pc EXCEPT ![p] = "write"]
    /\ UNCHANGED << counter, sem >>

\* Step 3: write back the incremented value
Write(p) ==
    /\ pc[p] = "write"
    /\ counter' = tmp[p] + 1
    /\ pc' = [pc EXCEPT ![p] = "release"]
    /\ UNCHANGED << sem, tmp >>

\* Step 4: release the semaphore and terminate
Release(p) ==
    /\ pc[p] = "release"
    /\ sem' = 1
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED << counter, tmp >>

proc(p) == Acquire(p) \/ Read(p) \/ Write(p) \/ Release(p)

AllDone == \A p \in Procs : pc[p] = "Done"

\* Allow stuttering once all processes have terminated (avoid deadlock)
Terminating == AllDone /\ UNCHANGED vars

Next == (\E p \in Procs : proc(p)) \/ Terminating

Fairness == \A p \in Procs : WF_vars(proc(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

MutualExclusion ==
    \A p, q \in Procs : (pc[p] \in CS /\ pc[q] \in CS) => p = q

SemaphoreConsistent ==
    (sem = 0) <=> (\E p \in Procs : pc[p] \in CS)

CorrectFinalValue == AllDone => counter = N

CounterBound == counter <= N

\* Liveness property

Termination == <>AllDone

EachProcessTerminates == \A p \in Procs : <>(pc[p] = "Done")

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ MutualExclusion /\ SemaphoreConsistent /\ CorrectFinalValue)
THEOREM Spec => Termination
=============================================================================