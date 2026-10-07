----------------------------- MODULE LamportFastMutex -----------------------------

EXTENDS Naturals

CONSTANT N

ProcSet == 1..N

VARIABLES x, y, b, pc, j, failed

Vars == << x, y, b, pc, j, failed >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in ProcSet |-> FALSE]
  /\ pc = [i \in ProcSet |-> "Try"]
  /\ j = [i \in ProcSet |-> 1]
  /\ failed = [i \in ProcSet |-> FALSE]

Try(i) ==
  /\ pc[i] = "Try"
  /\ x' = i
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "CheckY"]
  /\ UNCHANGED << y, j, failed >>

CheckY_Busy(i) ==
  /\ pc[i] = "CheckY"
  /\ y # 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "Backoff"]
  /\ UNCHANGED << x, y, j, failed >>

CheckY_Free(i) ==
  /\ pc[i] = "CheckY"
  /\ y = 0
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "CheckX"]
  /\ UNCHANGED << x, b, j, failed >>

Backoff_Wait(i) ==
  /\ pc[i] = "Backoff"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "Try"]
  /\ UNCHANGED << x, y, b, j, failed >>

CheckX_Fast(i) ==
  /\ pc[i] = "CheckX"
  /\ x = i
  /\ failed' = [failed EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ UNCHANGED << x, y, b, j >>

CheckX_Slow(i) ==
  /\ pc[i] = "CheckX"
  /\ x # i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ j' = [j EXCEPT ![i] = 1]
  /\ pc' = [pc EXCEPT ![i] = "WaitFlags"]
  /\ UNCHANGED << x, y, failed >>

WaitFlags_Advance(i) ==
  /\ pc[i] = "WaitFlags"
  /\ j[i] <= N
  /\ ~b[j[i]]
  /\ j' = [j EXCEPT ![i] = j[i] + 1]
  /\ UNCHANGED << x, y, b, pc, failed >>

WaitFlags_Done(i) ==
  /\ pc[i] = "WaitFlags"
  /\ j[i] > N
  /\ pc' = [pc EXCEPT ![i] = "CheckY2"]
  /\ UNCHANGED << x, y, b, j, failed >>

CheckY2_Win(i) ==
  /\ pc[i] = "CheckY2"
  /\ y = i
  /\ failed' = [failed EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ UNCHANGED << x, y, b, j >>

CheckY2_Lose(i) ==
  /\ pc[i] = "CheckY2"
  /\ y # i
  /\ pc' = [pc EXCEPT ![i] = "WaitY0AfterLose"]
  /\ UNCHANGED << x, y, b, j, failed >>

WaitY0AfterLose_Wait(i) ==
  /\ pc[i] = "WaitY0AfterLose"
  /\ y = 0
  /\ failed' = [failed EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "Try"]
  /\ UNCHANGED << x, y, b, j >>

CS_Exit(i) ==
  /\ pc[i] = "CS"
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ failed' = [failed EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "Try"]
  /\ UNCHANGED << x, j >>

Proc(i) ==
  Try(i)
  \/ CheckY_Busy(i) \/ CheckY_Free(i)
  \/ Backoff_Wait(i)
  \/ CheckX_Fast(i) \/ CheckX_Slow(i)
  \/ WaitFlags_Advance(i) \/ WaitFlags_Done(i)
  \/ CheckY2_Win(i) \/ CheckY2_Lose(i)
  \/ WaitY0AfterLose_Wait(i)
  \/ CS_Exit(i)

Next == \E i \in ProcSet: Proc(i)

TypeOK ==
  /\ x \in 0..N
  /\ y \in 0..N
  /\ b \in [ProcSet -> BOOLEAN]
  /\ pc \in [ProcSet -> {"Try","CheckY","Backoff","CheckX","WaitFlags","CheckY2","WaitY0AfterLose","CS"}]
  /\ j \in [ProcSet -> 1..(N + 1)]
  /\ failed \in [ProcSet -> BOOLEAN]

InCS(i) == pc[i] = "CS"

MutualExclusion ==
  \A i \in ProcSet: \A k \in ProcSet:
    (i # k) => ~(InCS(i) /\ InCS(k) /\ ~failed[i] /\ ~failed[k])

Invariant == TypeOK /\ MutualExclusion

SomeoneInCS == \E i \in ProcSet: InCS(i)

Contention == \E i \in ProcSet: \E k \in ProcSet: i # k /\ b[i] /\ b[k]

Liveness == []<>(\E i \in ProcSet: InCS(i))

Spec ==
  Init
  /\ [][Next]_Vars
  /\ \A i \in ProcSet: WF_Vars(Proc(i))

=============================================================================