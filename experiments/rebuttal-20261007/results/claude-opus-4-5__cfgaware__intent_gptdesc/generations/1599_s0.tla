---------------------------- MODULE MutualExclusion ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES
    pc,           \* Program counter for each process: "ncs", "try", "set_x", "set_y", "check_x", "wait", "cs", "exit"
    x,            \* Shared variable: last process to set x (0 means none)
    y,            \* Shared variable: last process to set y (0 means none)
    flag,         \* flag[i] = TRUE means process i is interested in CS
    waiting       \* waiting[i] = TRUE means process i is in waiting/spinning state

Procs == 1..N

TypeOK ==
    /\ pc \in [Procs -> {"ncs", "try", "set_x", "set_y", "check_x", "wait", "cs", "exit"}]
    /\ x \in 0..N
    /\ y \in 0..N
    /\ flag \in [Procs -> BOOLEAN]
    /\ waiting \in [Procs -> BOOLEAN]

Init ==
    /\ pc = [i \in Procs |-> "ncs"]
    /\ x = 0
    /\ y = 0
    /\ flag = [i \in Procs |-> FALSE]
    /\ waiting = [i \in Procs |-> FALSE]

\* Non-critical section: process decides to try entering CS
TryEnter(i) ==
    /\ pc[i] = "ncs"
    /\ pc' = [pc EXCEPT ![i] = "try"]
    /\ flag' = [flag EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<x, y, waiting>>

\* Set x to self
SetX(i) ==
    /\ pc[i] = "try"
    /\ x' = i
    /\ pc' = [pc EXCEPT ![i] = "set_x"]
    /\ UNCHANGED <<y, flag, waiting>>

\* Set y to self
SetY(i) ==
    /\ pc[i] = "set_x"
    /\ y' = i
    /\ pc' = [pc EXCEPT ![i] = "set_y"]
    /\ UNCHANGED <<x, flag, waiting>>

\* Check if x still equals self (fast path)
CheckX(i) ==
    /\ pc[i] = "set_y"
    /\ pc' = [pc EXCEPT ![i] = "check_x"]
    /\ UNCHANGED <<x, y, flag, waiting>>

\* Fast path succeeds: x = i, enter CS directly
FastPathSuccess(i) ==
    /\ pc[i] = "check_x"
    /\ x = i
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<x, y, flag, waiting>>

\* Fast path fails: x /= i, go to waiting state
FastPathFail(i) ==
    /\ pc[i] = "check_x"
    /\ x /= i
    /\ waiting' = [waiting EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ UNCHANGED <<x, y, flag>>

\* Waiting: check if y = 0 (no one else set y) - retry from beginning
WaitRetry(i) ==
    /\ pc[i] = "wait"
    /\ y = 0
    /\ waiting' = [waiting EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "try"]
    /\ UNCHANGED <<x, y, flag>>

\* Waiting: y /= 0, check if y = i (we are the chosen one) or wait for y to become i or 0
WaitSuccess(i) ==
    /\ pc[i] = "wait"
    /\ y = i
    /\ waiting' = [waiting EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<x, y, flag>>

\* Waiting: y /= 0 and y /= i, must wait for all other flags to be false
WaitForFlags(i) ==
    /\ pc[i] = "wait"
    /\ y /= 0
    /\ y /= i
    /\ \A j \in Procs \ {i} : flag[j] = FALSE
    /\ waiting' = [waiting EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<x, y, flag>>

\* Exit critical section
ExitCS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED <<x, y, flag, waiting>>

\* Complete exit: reset y if we set it, reset flag
CompleteExit(i) ==
    /\ pc[i] = "exit"
    /\ y' = IF y = i THEN 0 ELSE y
    /\ flag' = [flag EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED <<x, waiting>>

\* All actions for process i
ProcAction(i) ==
    \/ TryEnter(i)
    \/ SetX(i)
    \/ SetY(i)
    \/ CheckX(i)
    \/ FastPathSuccess(i)
    \/ FastPathFail(i)
    \/ WaitRetry(i)
    \/ WaitSuccess(i)
    \/ WaitForFlags(i)
    \/ ExitCS(i)
    \/ CompleteExit(i)

Next == \E i \in Procs : ProcAction(i)

\* Fairness: weak fairness on all process actions
Fairness == \A i \in Procs : WF_<<pc, x, y, flag, waiting>>(ProcAction(i))

Spec == Init /\ [][Next]_<<pc, x, y, flag, waiting>>

FairSpec == Spec /\ Fairness

\* Safety: Mutual Exclusion - at most one process in CS
MutualExclusion == Cardinality({i \in Procs : pc[i] = "cs"}) <= 1

Invariant == MutualExclusion /\ TypeOK

\* Liveness: If some process is trying, eventually some process enters CS
Trying == {i \in Procs : pc[i] /= "ncs"}

CondLiveness == (\E i \in Procs : pc[i] /= "ncs") ~> (\E i \in Procs : pc[i] = "cs")

================================================================================