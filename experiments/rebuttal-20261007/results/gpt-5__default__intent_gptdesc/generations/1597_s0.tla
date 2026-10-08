------------------------------ MODULE FastPathBackupME ------------------------------

EXTENDS Naturals, FiniteSets

(*
Parameterized mutual-exclusion with a fast doorway and a backup waiting protocol.
Atomicity assumptions:
- Individual reads/writes of shared variables are atomic.
- Each process step is atomic.
*)

CONSTANT N

ASSUME N \in Nat /\ N >= 1

Proc == 1..N

(*
Shared state:
- Doorway: global indicator that some process is in the fast doorway.
- Flag[i]: per-process intent flags.
Local per-process state:
- pc[i]: control location.
- WaitSet[i]: snapshot of processes to wait for in backup.
- TookDoor[i]: remembers if process i currently owns the fast doorway token.
*)

PCState == {"Idle", "DoorAttempt", "FastCheck", "BackupWait", "CS"}

VARIABLES
  pc,        \* [Proc -> PCState]
  Flag,      \* [Proc -> BOOLEAN]
  Doorway,   \* BOOLEAN
  WaitSet,   \* [Proc -> SUBSET Proc]
  TookDoor   \* [Proc -> BOOLEAN]

vars == << pc, Flag, Doorway, WaitSet, TookDoor >>

TypeOK ==
  /\ pc \in [Proc -> PCState]
  /\ Flag \in [Proc -> BOOLEAN]
  /\ Doorway \in BOOLEAN
  /\ WaitSet \in [Proc -> SUBSET Proc]
  /\ TookDoor \in [Proc -> BOOLEAN]

Init ==
  /\ pc = [i \in Proc |-> "Idle"]
  /\ Flag = [i \in Proc |-> FALSE]
  /\ Doorway = FALSE
  /\ WaitSet = [i \in Proc |-> {}]
  /\ TookDoor = [i \in Proc |-> FALSE]

(*
Helpers
*)
OthersClear(i) ==
  \A j \in Proc : j # i => ~Flag[j]

Snapshot(i) ==
  { j \in Proc : Flag[j] } \cup { j \in Proc : j < i }

BackupReady(i) ==
  \A j \in WaitSet[i] : ~Flag[j]

(*
Per-process actions
*)
Start(i) ==
  /\ pc[i] = "Idle"
  /\ pc' = [pc EXCEPT ![i] = "DoorAttempt"]
  /\ Flag' = [Flag EXCEPT ![i] = TRUE]
  /\ UNCHANGED << Doorway, WaitSet, TookDoor >>

FastDoorEnter(i) ==
  /\ pc[i] = "DoorAttempt"
  /\ ~Doorway
  /\ pc' = [pc EXCEPT ![i] = "FastCheck"]
  /\ Doorway' = TRUE
  /\ TookDoor' = [TookDoor EXCEPT ![i] = TRUE]
  /\ UNCHANGED << Flag, WaitSet >>

ContendToBackup(i) ==
  /\ pc[i] = "DoorAttempt"
  /\ Doorway
  /\ pc' = [pc EXCEPT ![i] = "BackupWait"]
  /\ WaitSet' = [WaitSet EXCEPT ![i] = Snapshot(i)]
  /\ TookDoor' = [TookDoor EXCEPT ![i] = FALSE]
  /\ UNCHANGED << Flag, Doorway >>

FastWinEnter(i) ==
  /\ pc[i] = "FastCheck"
  /\ OthersClear(i)
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ UNCHANGED << Flag, Doorway, WaitSet, TookDoor >>

FastLoseToBackup(i) ==
  /\ pc[i] = "FastCheck"
  /\ ~OthersClear(i)
  /\ pc' = [pc EXCEPT ![i] = "BackupWait"]
  /\ WaitSet' = [WaitSet EXCEPT ![i] = Snapshot(i)]
  /\ Doorway' = FALSE
  /\ TookDoor' = [TookDoor EXCEPT ![i] = FALSE]
  /\ UNCHANGED Flag

BackupEnter(i) ==
  /\ pc[i] = "BackupWait"
  /\ BackupReady(i)
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ UNCHANGED << Flag, Doorway, WaitSet, TookDoor >>

BackupRetry(i) ==
  /\ pc[i] = "BackupWait"
  /\ pc' = [pc EXCEPT ![i] = "Idle"]
  /\ Flag' = [Flag EXCEPT ![i] = FALSE]
  /\ WaitSet' = [WaitSet EXCEPT ![i] = {}]
  /\ TookDoor' = [TookDoor EXCEPT ![i] = FALSE]
  /\ UNCHANGED Doorway

LeaveCS(i) ==
  /\ pc[i] = "CS"
  /\ LET newDoor == IF TookDoor[i] THEN FALSE ELSE Doorway
     IN /\ Doorway' = newDoor
        /\ pc' = [pc EXCEPT ![i] = "Idle"]
        /\ Flag' = [Flag EXCEPT ![i] = FALSE]
        /\ WaitSet' = [WaitSet EXCEPT ![i] = {}]
        /\ TookDoor' = [TookDoor EXCEPT ![i] = FALSE]

ProcStep(i) ==
  Start(i)
  \/ FastDoorEnter(i)
  \/ ContendToBackup(i)
  \/ FastWinEnter(i)
  \/ FastLoseToBackup(i)
  \/ BackupEnter(i)
  \/ BackupRetry(i)
  \/ LeaveCS(i)

Next ==
  \E i \in Proc : ProcStep(i)

Spec ==
  Init /\ [][Next]_vars /\ (\A i \in Proc : WF_vars(ProcStep(i)))

(*
Safety: mutual exclusion
*)
MutualExclusion ==
  Cardinality({ i \in Proc : pc[i] = "CS" }) <= 1

(*
Liveness/progress: eventually some process enters the CS; and no global deadlock.
*)
Progress ==
  []<>(\E i \in Proc : pc[i] = "CS")

NoDeadlock ==
  []<>(Enabled Next)

=============================================================================