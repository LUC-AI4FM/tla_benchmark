---------------------------- MODULE TwoProcessCounter ----------------------------
EXTENDS Integers, TLC

CONSTANTS
    Target          \* Expected final value of the shared variable (intended: 2)

ASSUME Target \in Int

Procs == {1, 2}

Locations == {"Start", "Acquired", "Read", "Written", "Done"}

VARIABLES
    x,      \* the shared integer variable
    pc,     \* program counter of each process
    t,      \* local (private) register of each process
    lock    \* mutual-exclusion lock: 0 = free, otherwise id of the holder

vars == << x, pc, t, lock >>

-----------------------------------------------------------------------------
(* Initial condition: shared variable starts at 0, both processes at "Start", *)
(* local registers zeroed and the lock free.                                  *)
Init ==
    /\ x \in {0}
    /\ pc = [p \in Procs |-> "Start"]
    /\ t  = [p \in Procs |-> 0]
    /\ lock = 0

-----------------------------------------------------------------------------
(* Each step below is executed atomically; steps of different processes may  *)
(* interleave arbitrarily.                                                    *)

\* Step 1: acquire the lock (blocking until it is free)
Acquire(p) ==
    /\ pc[p] = "Start"
    /\ lock = 0
    /\ lock' = p
    /\ pc' = [pc EXCEPT ![p] = "Acquired"]
    /\ UNCHANGED << x, t >>

\* Step 2: read the shared variable into the local register
ReadX(p) ==
    /\ pc[p] = "Acquired"
    /\ t' = [t EXCEPT ![p] = x]
    /\ pc' = [pc EXCEPT ![p] = "Read"]
    /\ UNCHANGED << x, lock >>

\* Step 3: write back the incremented value (transient intermediate value)
WriteX(p) ==
    /\ pc[p] = "Read"
    /\ x' = t[p] + 1
    /\ pc' = [pc EXCEPT ![p] = "Written"]
    /\ UNCHANGED << t, lock >>

\* Step 4: release the lock and terminate
Release(p) ==
    /\ pc[p] = "Written"
    /\ lock' = 0
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED << x, t >>

Proc(p) ==
    \/ Acquire(p)
    \/ ReadX(p)
    \/ WriteX(p)
    \/ Release(p)

\* Stuttering once both processes have terminated (avoids spurious deadlock)
Terminating ==
    /\ \A p \in Procs : pc[p] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Procs : Proc(p)
    \/ Terminating

\* Weak fairness for each process individually
Fairness == \A p \in Procs : WF_vars(Proc(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ x \in Int
    /\ pc \in [Procs -> Locations]
    /\ t \in [Procs -> Int]
    /\ lock \in {0} \cup Procs

\* Mutual exclusion of the critical section
MutualExclusion ==
    \A p, q \in Procs :
        (p # q) => ~(pc[p] \in {"Acquired", "Read", "Written"}
                     /\ pc[q] \in {"Acquired", "Read", "Written"})

AllDone == \A p \in Procs : pc[p] = "Done"

\* Primary safety property: at joint termination the shared value equals Target
FinalValueCorrect == AllDone => (x = Target)

\* Equivalent explicit form: no reachable state is terminated with a wrong value
NoBadFinalState == ~(AllDone /\ x # Target)

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Each process eventually terminates
EachTerminates == \A p \in Procs : <>(pc[p] = "Done")

\* Both processes eventually terminate (and stay terminated)
BothTerminate == <>[]AllDone

\* Once both are done, the final value is permanently Target
EventuallyCorrect == <>[](AllDone /\ x = Target)

=============================================================================