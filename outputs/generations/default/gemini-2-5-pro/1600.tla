------------------------- MODULE FastMutex -------------------------
EXTENDS Integers, TLC

CONSTANTS N
ASSUME N \in Nat \ {0}

Procs == 1..N

VARIABLES 
    \* Shared variables
    x,      \* Indicates the last process to start the protocol
    y,      \* Indicates the process holding the lock (or trying to)
    b,      \* b[i] is TRUE if process i has intent to enter CS
    
    \* Per-process local variables
    pc,     \* Program counter for each process
    j,      \* Loop counter for the slow path for each process
    failed  \* Flag indicating if a process failed the fast path

vars == <<x, y, b, pc, j, failed>>

Labels == {"ncs", "CheckY", "AwaitY", "CheckX", "AwaitB", "CheckY2", "cs"}

TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> Labels]
    /\ j \in [Procs -> 1..(N + 1)]
    /\ failed \in [Procs -> BOOLEAN]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "ncs"]
    /\ j = [i \in Procs |-> 1]
    /\ failed = [i \in Procs |-> FALSE]

\* Actions for process i \in Procs

\* A process in its non-critical section decides to enter the critical section.
\* It sets its intent flag b[i], sets x to its own id, and proceeds to CheckY.
Start(i) ==
    /\ pc[i] = "ncs"
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ x' = i
    /\ failed' = [failed EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "CheckY"]
    /\ UNCHANGED <<y, j>>

\* The process checks if there is contention (y /= 0).
\* If not (fast path), it sets y to its own id and proceeds to CheckX.
\* If so (contention), it retracts its intent and waits for y to become 0.
CheckY(i) ==
    /\ pc[i] = "CheckY"
    /\ \/ /\ y = 0  \* Fast path continues
          /\ y' = i
          /\ pc' = [pc EXCEPT ![i] = "CheckX"]
          /\ UNCHANGED <<x, b, j, failed>>
       \/ /\ y /= 0 \* Contention
          /\ b' = [b EXCEPT ![i] = FALSE]
          /\ pc' = [pc EXCEPT ![i] = "AwaitY"]
          /\ UNCHANGED <<x, y, j, failed>>

\* The process waits for y to be cleared, then restarts the protocol.
AwaitY(i) ==
    /\ pc[i] = "AwaitY"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED <<x, y, b, j, failed>>

\* The process checks if x is still its own id.
\* If so (fast path success), it enters the critical section.
\* If not, another process has intervened. It enters the slow path.
CheckX(i) ==
    /\ pc[i] = "CheckX"
    /\ \/ /\ x = i  \* Fast path success
          /\ pc' = [pc EXCEPT ![i] = "cs"]
          /\ UNCHANGED <<x, y, b, j, failed>>
       \/ /\ x /= i \* Slow path
          /\ failed' = [failed EXCEPT ![i] = TRUE]
          /\ b' = [b EXCEPT ![i] = FALSE]
          /\ j' = [j EXCEPT ![i] = 1]
          /\ pc' = [pc EXCEPT ![i] = "AwaitB"]
          /\ UNCHANGED <<x, y>>

\* Slow path: the process iterates from j=1 to N, waiting for each b[j] to be FALSE.
AwaitB(i) ==
    /\ pc[i] = "AwaitB"
    /\ \/ /\ j[i] <= N  \* Loop continues
          /\ b[j[i]] = FALSE
          /\ j' = [j EXCEPT ![i] = j[i] + 1]
          /\ pc' = pc \* Stay at AwaitB to check next j
          /\ UNCHANGED <<x, y, b, failed>>
       \/ /\ j[i] > N   \* Loop finishes
          /\ pc' = [pc EXCEPT ![i] = "CheckY2"]
          /\ UNCHANGED <<x, y, b, j, failed>>

\* After the slow path wait, the process re-evaluates y.
\* If y is not its own id, it means another process may have the lock, so it must restart.
\* If y is still its own id, it can proceed to the critical section.
CheckY2(i) ==
    /\ pc[i] = "CheckY2"
    /\ \/ /\ y /= i
          /\ pc' = [pc EXCEPT ![i] = "AwaitY"]
          /\ UNCHANGED <<x, y, b, j, failed>>
       \/ /\ y = i
          /\ pc' = [pc EXCEPT ![i] = "cs"]
          /\ UNCHANGED <<x, y, b, j, failed>>

\* The process exits the critical section, clearing y and its intent flag.
ExitCS(i) ==
    /\ pc[i] = "cs"
    /\ y' = 0
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED <<x, j, failed>>

\* A process step is the disjunction of all its possible actions.
P(i) ==
    \/ Start(i)
    \/ CheckY(i)
    \/ AwaitY(i)
    \/ CheckX(i)
    \/ AwaitB(i)
    \/ CheckY2(i)
    \/ ExitCS(i)

Next == \E i \in Procs : P(i)

\* Fairness condition: Each process gets to take a step if it's enabled.
Fairness == \A i \in Procs : WF_vars(P(i))

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Properties to be checked by the model checker.

\* Safety: At most one process is in the critical section at any time.
MutualExclusion ==
    \A i, k \in Procs : (i /= k) => (pc[i] /= "cs" \/ pc[k] /= "cs")

\* Liveness: Infinitely often, some process is in the critical section.
\* This should be checked under the fairness assumption.
Liveness == []<>(\E i \in Procs : pc[i] = "cs")

=============================================================================