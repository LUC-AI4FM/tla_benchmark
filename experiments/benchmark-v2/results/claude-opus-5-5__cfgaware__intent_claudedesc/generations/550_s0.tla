---------------------------- MODULE RoundRobinMutex ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N > 0

Procs == 0 .. (N - 1)

VARIABLES pc, turn

vars == <<pc, turn>>

\* Process p is currently executing in the critical section
cs(p) == pc[p] = "cs"

TypeOK ==
    /\ pc \in [Procs -> {"ncs", "wait", "cs"}]
    /\ turn \in Procs

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ turn \in Procs

\* Non-critical section work finished; start trying to enter
NonCrit(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED turn

\* Enter the critical section only when it is p's turn
Enter(p) ==
    /\ pc[p] = "wait"
    /\ turn = p
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED turn

\* Leave the critical section and pass the turn to the next process
Exit(p) ==
    /\ cs(p)
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ turn' = (p + 1) % N

proc(p) == NonCrit(p) \/ Enter(p) \/ Exit(p)

Next == \E p \in Procs : proc(p)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A p \in Procs : WF_vars(proc(p))

-------------------------------------------------------------------------------
\* Correctness properties

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(cs(p) /\ cs(q))

TurnInvariant ==
    \A p \in Procs : cs(p) => turn = p

StarvationFreedom ==
    \A p \in Procs : (pc[p] = "wait") ~> cs(p)

\* Entries happen only for the process holding the turn, and the turn
\* advances cyclically (p -> p+1 mod N) only on exit.
StrictOrdering ==
    [][ /\ \A p \in Procs : (~cs(p) /\ pc'[p] = "cs") => p = turn
        /\ (turn' # turn) => (turn' = (turn + 1) % N /\ pc[turn] = "cs")
      ]_vars

THEOREM Spec => [](TypeOK /\ MutualExclusion)
=============================================================================