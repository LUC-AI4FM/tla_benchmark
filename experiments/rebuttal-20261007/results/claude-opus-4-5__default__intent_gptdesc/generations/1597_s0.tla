-------------------------------- MODULE FastMutex --------------------------------
(***************************************************************************)
(* A parameterized mutual exclusion algorithm for N concurrent processes   *)
(* implementing a fast path with a backup waiting protocol.                *)
(*                                                                         *)
(* Atomicity assumptions:                                                  *)
(* - Individual reads and writes of shared variables are atomic            *)
(* - Each process step (action) is atomic                                  *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS N  \* Number of processes

ASSUME N \in Nat /\ N > 0

Procs == 1..N  \* Set of process identifiers

(***************************************************************************)
(* Variables:                                                              *)
(* - pc: program counter for each process                                  *)
(* - flag: per-process flag indicating intent to enter critical section    *)
(* - gate: global indicator - 0 means no one in fast path, >0 means        *)
(*         process gate is attempting fast entry                           *)
(* - waiting: per-process indicator that process is in backup protocol     *)
(***************************************************************************)

VARIABLES pc, flag, gate, waiting

vars == <<pc, flag, gate, waiting>>

(***************************************************************************)
(* Program counter states:                                                 *)
(* - "idle": not attempting to enter CS                                    *)
(* - "set_flag": setting own flag to indicate intent                       *)
(* - "try_fast": attempting fast path entry                                *)
(* - "check_gate": checking if won fast path race                          *)
(* - "backup_start": entering backup protocol after losing fast race       *)
(* - "backup_wait": waiting in backup protocol                             *)
(* - "cs": in critical section                                             *)
(* - "exit": exiting critical section                                      *)
(***************************************************************************)

PCStates == {"idle", "set_flag", "try_fast", "check_gate", 
             "backup_start", "backup_wait", "cs", "exit"}

TypeOK ==
    /\ pc \in [Procs -> PCStates]
    /\ flag \in [Procs -> BOOLEAN]
    /\ gate \in (Procs \cup {0})
    /\ waiting \in [Procs -> BOOLEAN]

(***************************************************************************)
(* Initial state: all processes idle, no flags set, gate clear             *)
(***************************************************************************)

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ flag = [p \in Procs |-> FALSE]
    /\ gate = 0
    /\ waiting = [p \in Procs |-> FALSE]

(***************************************************************************)
(* Process actions                                                         *)
(***************************************************************************)

(* Process p starts attempting to enter critical section by setting flag *)
StartAttempt(p) ==
    /\ pc[p] = "idle"
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ pc' = [pc EXCEPT ![p] = "set_flag"]
    /\ UNCHANGED <<gate, waiting>>

(* Process p tries to claim the fast path by setting gate *)
TryFastPath(p) ==
    /\ pc[p] = "set_flag"
    /\ gate = 0  \* No one else in fast path
    /\ gate' = p
    /\ pc' = [pc EXCEPT ![p] = "try_fast"]
    /\ UNCHANGED <<flag, waiting>>

(* Process p detects contention and goes to backup protocol *)
DetectContention(p) ==
    /\ pc[p] = "set_flag"
    /\ gate /= 0  \* Someone else in fast path
    /\ pc' = [pc EXCEPT ![p] = "backup_start"]
    /\ UNCHANGED <<flag, gate, waiting>>

(* Process p checks if it still holds the gate (won fast race) *)
CheckGateWin(p) ==
    /\ pc[p] = "try_fast"
    /\ gate = p  \* Still holds gate
    \* Check no other process has flag set (fast path success condition)
    /\ \A q \in Procs \ {p} : ~flag[q]
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED <<flag, gate, waiting>>

(* Process p finds another flag set, must use backup protocol *)
CheckGateLose(p) ==
    /\ pc[p] = "try_fast"
    /\ \E q \in Procs \ {p} : flag[q]
    /\ pc' = [pc EXCEPT ![p] = "check_gate"]
    /\ UNCHANGED <<flag, gate, waiting>>

(* Process p releases gate and enters backup protocol *)
ReleaseGateToBackup(p) ==
    /\ pc[p] = "check_gate"
    /\ gate' = 0
    /\ pc' = [pc EXCEPT ![p] = "backup_start"]
    /\ UNCHANGED <<flag, waiting>>

(* Process p enters backup waiting mode *)
EnterBackupWait(p) ==
    /\ pc[p] = "backup_start"
    /\ waiting' = [waiting EXCEPT ![p] = TRUE]
    /\ pc' = [pc EXCEPT ![p] = "backup_wait"]
    /\ UNCHANGED <<flag, gate>>

(* Process p in backup protocol checks if it can proceed *)
(* Can proceed when all lower-indexed processes have cleared flags *)
(* and no higher-indexed process is in CS *)
BackupProceed(p) ==
    /\ pc[p] = "backup_wait"
    \* All processes with lower index have cleared their flags or are not waiting
    /\ \A q \in 1..(p-1) : (~flag[q] \/ ~waiting[q])
    \* No process currently in critical section
    /\ \A q \in Procs \ {p} : pc[q] /= "cs"
    /\ waiting' = [waiting EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED <<flag, gate>>

(* Process p exits critical section *)
ExitCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<flag, gate, waiting>>

(* Process p clears its flag and returns to idle *)
ClearAndIdle(p) ==
    /\ pc[p] = "exit"
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ gate' = IF gate = p THEN 0 ELSE gate
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<waiting>>

(* Retry: process p gives up current attempt and restarts *)
(* This handles the case where a process needs to reattempt *)
Retry(p) ==
    /\ pc[p] \in {"backup_start", "backup_wait"}
    /\ waiting' = [waiting EXCEPT ![p] = FALSE]
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<gate>>

(***************************************************************************)
(* Next state relation                                                     *)
(***************************************************************************)

ProcessAction(p) ==
    \/ StartAttempt(p)
    \/ TryFastPath(p)
    \/ DetectContention(p)
    \/ CheckGateWin(p)
    \/ CheckGateLose(p)
    \/ ReleaseGateToBackup(p)
    \/ EnterBackupWait(p)
    \/ BackupProceed(p)
    \/ ExitCS(p)
    \/ ClearAndIdle(p)

Next == \E p \in Procs : ProcessAction(p)

(***************************************************************************)
(* Fairness: Weak fairness for each process's actions ensures progress     *)
(***************************************************************************)

Fairness == \A p \in Procs : WF_vars(ProcessAction(p))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety Properties                                                       *)
(***************************************************************************)

(* Mutual Exclusion: At most one process in critical section *)
MutualExclusion ==
    \A p, q \in Procs : (p /= q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* Alternative formulation *)
AtMostOneInCS == Cardinality({p \in Procs : pc[p] = "cs"}) <= 1

(***************************************************************************)
(* Liveness Properties                                                     *)
(***************************************************************************)

(* Progress: Eventually some process enters the critical section *)
(* (Assuming the system keeps running) *)
Progress == []<>(\E p \in Procs : pc[p] = "cs")

(* No Deadlock: It's always possible for some process to make progress *)
NoDeadlock == 
    \A p \in Procs : (pc[p] /= "idle") => 
        <>(\E q \in Procs : pc[q] = "cs" \/ pc[q] = "idle")

(* Starvation Freedom: Every process that starts eventually enters CS *)
(* (This is a stronger property) *)
StarvationFreedom ==
    \A p \in Procs : (pc[p] = "set_flag") ~> (pc[p] = "cs")

(* The system is not permanently stuck *)
NotStuck == []<>(ENABLED Next)

(***************************************************************************)
(* Invariants for checking                                                 *)
(***************************************************************************)

(* If a process is in CS, its flag should be set *)
FlagInvariant ==
    \A p \in Procs : (pc[p] = "cs") => flag[p]

(* Gate is either 0 or points to a valid process *)
GateInvariant ==
    gate \in (Procs \cup {0})

(* Combined safety invariant *)
SafetyInvariant ==
    /\ TypeOK
    /\ MutualExclusion
    /\ FlagInvariant
    /\ GateInvariant

================================================================================