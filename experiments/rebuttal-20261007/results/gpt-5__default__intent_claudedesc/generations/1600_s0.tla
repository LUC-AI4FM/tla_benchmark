------------------------------ MODULE LamportFastMutex ------------------------------

EXTENDS Naturals

CONSTANT N
ASSUME N \in Nat \ {0} /\ N = 3

(*
  Lamport's Fast Mutex algorithm for N processes.
  Shared variables:
    x, y \in {0} \cup ProcSet
    flag \in [ProcSet -> BOOLEAN]
  Per-process control locations in pc[i].
*)

ProcSet == 1..N
ValSet  == {0} \cup ProcSet

VARIABLES x, y, flag, pc

vars == << x, y, flag, pc >>

PCStates == {"Idle","CheckY","CheckX","WaitFlags","CheckY2","WaitY0","CS","Exit2"}

TypeOK ==
  /\ x \in ValSet
  /\ y \in ValSet
  /\ flag \in [ProcSet -> BOOLEAN]
  /\ pc \in [ProcSet -> PCStates]

Init ==
  /\ x = 0
  /\ y = 0
  /\ flag = [i \in ProcSet |-> FALSE]
  /\ pc = [i \in ProcSet |-> "Idle"]
  /\ TypeOK

AnnounceStep(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "Idle"
  /\ x' = i
  /\ flag' = [flag EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "CheckY"]
  /\ UNCHANGED y

CheckY_Busy(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "CheckY"
  /\ y # 0
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "WaitY0"]
  /\ UNCHANGED << x, y >>

CheckY_Free(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "CheckY"
  /\ y = 0
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "CheckX"]
  /\ UNCHANGED << x, flag >>

CheckX_Fast(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "CheckX"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ UNCHANGED << x, y, flag >>

CheckX_Interfered(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "CheckX"
  /\ x # i
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "WaitFlags"]
  /\ UNCHANGED << x, y >>

WaitFlags_Done(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "WaitFlags"
  /\ \A j \in ProcSet \ {i}: flag[j] = FALSE
  /\ pc' = [pc EXCEPT ![i] = "CheckY2"]
  /\ UNCHANGED << x, y, flag >>

CheckY2_Hold(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "CheckY2"
  /\ y = i
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ UNCHANGED << x, y, flag >>

CheckY2_NotHold(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "CheckY2"
  /\ y # i
  /\ pc' = [pc EXCEPT ![i] = "WaitY0"]
  /\ UNCHANGED << x, y, flag >>

WaitY0_Done(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "WaitY0"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "Idle"]
  /\ UNCHANGED << x, y, flag >>

Exit_ClearY(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "CS"
  /\ y' = 0
  /\ pc' = [pc EXCEPT ![i] = "Exit2"]
  /\ UNCHANGED << x, flag >>

Exit_ClearFlag(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "Exit2"
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "Idle"]
  /\ UNCHANGED << x, y >>

Proc(i) ==
  AnnounceStep(i)
  \/ CheckY_Busy(i)
  \/ CheckY_Free(i)
  \/ CheckX_Fast(i)
  \/ CheckX_Interfered(i)
  \/ WaitFlags_Done(i)
  \/ CheckY2_Hold(i)
  \/ CheckY2_NotHold(i)
  \/ WaitY0_Done(i)
  \/ Exit_ClearY(i)
  \/ Exit_ClearFlag(i)

Next ==
  \E i \in ProcSet: Proc(i)

Spec ==
  Init /\ [][Next]_vars /\ (\A i \in ProcSet: WF_vars(Proc(i)))

MutualExclusion ==
  \A i, j \in ProcSet: i # j => ~(pc[i] = "CS" /\ pc[j] = "CS")

Progress ==
  []<>(\E i \in ProcSet: pc[i] = "CS")

=============================================================================