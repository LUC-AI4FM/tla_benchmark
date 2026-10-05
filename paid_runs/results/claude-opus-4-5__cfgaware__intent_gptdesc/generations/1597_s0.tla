---------------------------- MODULE MutualExclusion ----------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES
    pc,           \* Program counter for each process: "idle", "setFlag", "checkDoor", "enterFast", "backup", "waiting", "cs", "exitCS"
    door,         \* Global indicator: 0 means no one in doorway, otherwise process id in doorway
    flag,         \* Array of per-process flags indicating intent
    waiting_for   \* For backup protocol: which process index we're waiting for

vars == <<pc, door, flag, waiting_for>>

Procs == 1..N

TypeOK ==
    /\ pc \in [Procs -> {"idle", "setFlag", "checkDoor", "enterFast", "backup", "waiting", "cs", "exitCS", "clearDoor"}]
    /\ door \in 0..N
    /\ flag \in [Procs -> BOOLEAN]
    /\ waiting_for \in [Procs -> 0..N]

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ door = 0
    /\ flag = [p \in Procs |-> FALSE]
    /\ waiting_for = [p \in Procs |-> 0]

\* Process p starts trying to enter critical section
StartTrying(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "setFlag"]
    /\ UNCHANGED <<door, flag, waiting_for>>

\* Process p sets its flag to indicate intent
SetFlag(p) ==
    /\ pc[p] = "setFlag"
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ pc' = [pc EXCEPT ![p] = "checkDoor"]
    /\ UNCHANGED <<door, waiting_for>>

\* Process p checks if doorway is free and tries to claim it
CheckDoor(p) ==
    /\ pc[p] = "checkDoor"
    /\ IF door = 0
       THEN /\ door' = p
            /\ pc' = [pc EXCEPT ![p] = "enterFast"]
            /\ UNCHANGED <<flag, waiting_for>>
       ELSE /\ pc' = [pc EXCEPT ![p] = "backup"]
            /\ UNCHANGED <<door, flag, waiting_for>>

\* Fast path: check if we're still the door holder and no other flags
EnterFast(p) ==
    /\ pc[p] = "enterFast"
    /\ LET otherFlags == {q \in Procs : q # p /\ flag[q]}
       IN IF door = p /\ otherFlags = {}
          THEN /\ pc' = [pc EXCEPT ![p] = "cs"]
               /\ UNCHANGED <<door, flag, waiting_for>>
          ELSE /\ pc' = [pc EXCEPT ![p] = "clearDoor"]
               /\ UNCHANGED <<door, flag, waiting_for>>

\* Clear door before going to backup
ClearDoor(p) ==
    /\ pc[p] = "clearDoor"
    /\ IF door = p
       THEN door' = 0
       ELSE door' = door
    /\ pc' = [pc EXCEPT ![p] = "backup"]
    /\ UNCHANGED <<flag, waiting_for>>

\* Backup protocol: start waiting for lower-indexed processes
BackupStart(p) ==
    /\ pc[p] = "backup"
    /\ waiting_for' = [waiting_for EXCEPT ![p] = 1]
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<door, flag>>

\* Waiting: check processes with lower or equal index (except self)
WaitingStep(p) ==
    /\ pc[p] = "waiting"
    /\ LET w == waiting_for[p]
       IN IF w > N
          THEN \* Done waiting, can enter CS
               /\ pc' = [pc EXCEPT ![p] = "cs"]
               /\ UNCHANGED <<door, flag, waiting_for>>
          ELSE IF w = p
               THEN \* Skip self
                    /\ waiting_for' = [waiting_for EXCEPT ![p] = w + 1]
                    /\ UNCHANGED <<pc, door, flag>>
               ELSE IF ~flag[w]
                    THEN \* Process w has cleared flag, move to next
                         /\ waiting_for' = [waiting_for EXCEPT ![p] = w + 1]
                         /\ UNCHANGED <<pc, door, flag>>
                    ELSE \* Still waiting for process w
                         /\ UNCHANGED vars

\* Process is in critical section
InCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exitCS"]
    /\ UNCHANGED <<door, flag, waiting_for>>

\* Exit critical section
ExitCS(p) ==
    /\ pc[p] = "exitCS"
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ IF door = p
       THEN door' = 0
       ELSE door' = door
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<waiting_for>>

\* All actions for process p
ProcAction(p) ==
    \/ StartTrying(p)
    \/ SetFlag(p)
    \/ CheckDoor(p)
    \/ EnterFast(p)
    \/ ClearDoor(p)
    \/ BackupStart(p)
    \/ WaitingStep(p)
    \/ InCS(p)
    \/ ExitCS(p)

Next == \E p \in Procs : ProcAction(p)

\* Fairness: weak fairness for each process's actions
Fairness == \A p \in Procs : WF_vars(ProcAction(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Mutual Exclusion - at most one process in CS
MutualExclusion == Cardinality({p \in Procs : pc[p] = "cs"}) <= 1

\* No deadlock: if all processes are trying, someone can make progress
NoDeadlock == 
    (\A p \in Procs : pc[p] # "idle") => 
    (\E p \in Procs : ENABLED(ProcAction(p)))

Invariant == MutualExclusion /\ TypeOK

\* Liveness: eventually some process enters the critical section
\* If any process starts trying, eventually some process enters CS
Liveness == []<>(\E p \in Procs : pc[p] = "cs")

=============================================================================