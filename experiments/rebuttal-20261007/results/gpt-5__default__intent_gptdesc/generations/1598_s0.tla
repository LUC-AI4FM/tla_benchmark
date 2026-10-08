----------------------------- MODULE FastMutex -----------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 1

(*
  Lamport's Fast Mutual Exclusion for N processes.
  Shared registers x, y in {0} \cup Proc; per-process boolean flag.
  Local control pc[i] encodes protocol location; k[i] stores a snapshot of x
  to spin on flag[k[i]] during the back-off path.
*)

Proc    == 1..N
RegDom  == Proc \cup {0}
States  == {"Try","SetX","CheckY1","SetY","CheckX2",
            "WaitY0_1","WaitFlagKFalse","CheckY2","WaitY0_2","CS"}

VARIABLES pc, flag, x, y, k

vars == << pc, flag, x, y, k >>

TypeOK ==
  /\ pc \in [Proc -> States]
  /\ flag \in [Proc -> BOOLEAN]
  /\ x \in RegDom
  /\ y \in RegDom
  /\ k \in [Proc -> RegDom]

Init ==
  /\ pc   = [ i \in Proc |-> "Try" ]
  /\ flag = [ i \in Proc |-> FALSE ]
  /\ x = 0
  /\ y = 0
  /\ k = [ i \in Proc |-> 0 ]

(*
  Process i actions (atomic steps)
*)

TryToSetIntent(i) ==
  /\ i \in Proc
  /\ pc[i] = "Try"
  /\ pc'   = [pc EXCEPT ![i] = "SetX"]
  /\ flag' = [flag EXCEPT ![i] = TRUE]
  /\ UNCHANGED << x, y, k >>

SetXStep(i) ==
  /\ i \in Proc
  /\ pc[i] = "SetX"
  /\ x'  = i
  /\ pc' = [pc EXCEPT ![i] = "CheckY1"]
  /\ UNCHANGED << y, flag, k >>

CheckY1Abort(i) ==
  /\ i \in Proc
  /\ pc[i] = "CheckY1"
  /\ y # 0
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ pc'   = [pc EXCEPT ![i] = "WaitY0_1"]
  /\ UNCHANGED << x, y, k >>

CheckY1Proceed(i) ==
  /\ i \in Proc
  /\ pc[i] = "CheckY1"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "SetY"]
  /\ UNCHANGED << x, y, flag, k >>

SetYStep(i) ==
  /\ i \in Proc
  /\ pc[i] = "SetY"
  /\ y'  = i
  /\ pc' = [pc EXCEPT ![i] = "CheckX2"]
  /\ UNCHANGED << x, flag, k >>

CheckX2Abort(i) ==
  /\ i \in Proc
  /\ pc[i] = "CheckX2"
  /\ x # i
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ k'    = [k EXCEPT ![i] = x]
  /\ pc'   = [pc EXCEPT ![i] = "WaitFlagKFalse"]
  /\ UNCHANGED << x, y >>

CheckX2Proceed(i) ==
  /\ i \in Proc
  /\ pc[i] = "CheckX2"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ UNCHANGED << x, y, flag, k >>

WaitY0_1_Done(i) ==
  /\ i \in Proc
  /\ pc[i] = "WaitY0_1"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "Try"]
  /\ UNCHANGED << x, y, flag, k >>

WaitFlagKFalse_Done(i) ==
  /\ i \in Proc
  /\ pc[i] = "WaitFlagKFalse"
  /\ k[i] \in Proc
  /\ flag[k[i]] = FALSE
  /\ k'  = [k EXCEPT ![i] = 0]
  /\ pc' = [pc EXCEPT ![i] = "CheckY2"]
  /\ UNCHANGED << x, y, flag >>

CheckY2Enter(i) ==
  /\ i \in Proc
  /\ pc[i] = "CheckY2"
  /\ y = i
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ UNCHANGED << x, y, flag, k >>

CheckY2Wait(i) ==
  /\ i \in Proc
  /\ pc[i] = "CheckY2"
  /\ y # i
  /\ pc' = [pc EXCEPT ![i] = "WaitY0_2"]
  /\ UNCHANGED << x, y, flag, k >>

WaitY0_2_Done(i) ==
  /\ i \in Proc
  /\ pc[i] = "WaitY0_2"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "Try"]
  /\ UNCHANGED << x, y, flag, k >>

ExitCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "CS"
  /\ y'    = 0
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ k'    = [k EXCEPT ![i] = 0]
  /\ pc'   = [pc EXCEPT ![i] = "Try"]
  /\ UNCHANGED << x >>

ProcStep(i) ==
     TryToSetIntent(i)
  \/ SetXStep(i)
  \/ CheckY1Abort(i)
  \/ CheckY1Proceed(i)
  \/ SetYStep(i)
  \/ CheckX2Abort(i)
  \/ CheckX2Proceed(i)
  \/ WaitY0_1_Done(i)
  \/ WaitFlagKFalse_Done(i)
  \/ CheckY2Enter(i)
  \/ CheckY2Wait(i)
  \/ WaitY0_2_Done(i)
  \/ ExitCS(i)

Next == \E i \in Proc: ProcStep(i)

Fairness == \A i \in Proc: WF_vars(ProcStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

(*
  Safety: Mutual exclusion (no two processes in CS simultaneously)
*)
MutualExclusion ==
  \A i \in Proc: \A j \in Proc:
    i # j => ~(pc[i] = "CS" /\ pc[j] = "CS")

(*
  Liveness:
    - System-wide: infinitely often, some process enters CS.
    - Optional per-process: each process enters CS infinitely often.
*)
SomeProcessEventuallyCS ==
  [](<> (\E i \in Proc: pc[i] = "CS"))

PerProcessEventuallyCS(i) ==
  [](<> (pc[i] = "CS"))

AllProcessesEventuallyCS ==
  \A i \in Proc: PerProcessEventuallyCS(i)

THEOREM Spec => []TypeOK
THEOREM Spec => []MutualExclusion
THEOREM Spec => SomeProcessEventuallyCS
THEOREM Spec => AllProcessesEventuallyCS

=============================================================================