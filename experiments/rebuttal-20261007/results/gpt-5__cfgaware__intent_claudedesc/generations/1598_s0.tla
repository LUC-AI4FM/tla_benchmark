------------------------------ MODULE FastMutex ------------------------------

EXTENDS Naturals

CONSTANT N

(*
  Processes are identified by integers 1..N.
*)
Proc == 1..N

(*
  State variables:
    x, y: integers in 0..N (0 means "none")
    b: boolean array over Proc
    pc: per-process control location
*)
VARIABLES x, y, b, pc

PcStates == {"try", "setX", "checkY", "waitY0", "setY", "checkX",
             "waitOthers", "cs", "clearB"}

vars == << x, y, b, pc >>

TypeOK ==
  /\ x \in 0..N
  /\ y \in 0..N
  /\ b \in [Proc -> BOOLEAN]
  /\ pc \in [Proc -> PcStates]

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Proc |-> FALSE]
  /\ pc = [i \in Proc |-> "try"]

(*
  Per-process actions implementing a fast-path mutex protocol (Lamport-style).
*)
Try1(i) ==
  /\ i \in Proc
  /\ pc[i] = "try"
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "setX"]
  /\ UNCHANGED << x, y >>

SetX(i) ==
  /\ i \in Proc
  /\ pc[i] = "setX"
  /\ x' = i
  /\ pc' = [pc EXCEPT ![i] = "checkY"]
  /\ UNCHANGED << y, b >>

CheckY_OK(i) ==
  /\ i \in Proc
  /\ pc[i] = "checkY"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "setY"]
  /\ UNCHANGED << x, y, b >>

CheckY_Contend(i) ==
  /\ i \in Proc
  /\ pc[i] = "checkY"
  /\ y # 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "waitY0"]
  /\ UNCHANGED << x, y >>

WaitY0(i) ==
  /\ i \in Proc
  /\ pc[i] = "waitY0"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "try"]
  /\ UNCHANGED << x, y, b >>

SetY(i) ==
  /\ i \in Proc
  /\ pc[i] = "setY"
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "checkX"]
  /\ UNCHANGED << x, b >>

CheckX_OK(i) ==
  /\ i \in Proc
  /\ pc[i] = "checkX"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b >>

CheckX_Contend(i) ==
  /\ i \in Proc
  /\ pc[i] = "checkX"
  /\ x # i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "waitOthers"]
  /\ UNCHANGED << x, y >>

WaitOthers_ToCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "waitOthers"
  /\ \A k \in Proc \ {i} : ~b[k]
  /\ y = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b >>

WaitOthers_ToWaitY(i) ==
  /\ i \in Proc
  /\ pc[i] = "waitOthers"
  /\ \A k \in Proc \ {i} : ~b[k]
  /\ y # i
  /\ pc' = [pc EXCEPT ![i] = "waitY0"]
  /\ UNCHANGED << x, y, b >>

CS_Leave1(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ y' = 0
  /\ pc' = [pc EXCEPT ![i] = "clearB"]
  /\ UNCHANGED << x, b >>

ClearB(i) ==
  /\ i \in Proc
  /\ pc[i] = "clearB"
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "try"]
  /\ UNCHANGED << x, y >>

ProcStep(i) ==
  Try1(i)
  \/ SetX(i)
  \/ CheckY_OK(i)
  \/ CheckY_Contend(i)
  \/ WaitY0(i)
  \/ SetY(i)
  \/ CheckX_OK(i)
  \/ CheckX_Contend(i)
  \/ WaitOthers_ToCS(i)
  \/ WaitOthers_ToWaitY(i)
  \/ CS_Leave1(i)
  \/ ClearB(i)

Next ==
  \E i \in Proc : ProcStep(i)

(*
  Critical section predicate and mutual exclusion invariant.
*)
Crit(i) == pc[i] = "cs"

MutualExclusion ==
  \A i, j \in Proc : i # j => ~(Crit(i) /\ Crit(j))

Invariant == MutualExclusion

(*
  Weak fairness on every process's step.
*)
Spec ==
  Init
  /\ [][Next]_vars
  /\ \A i \in Proc : WF_vars(ProcStep(i))

(*
  Liveness: some process enters the critical section infinitely often.
*)
Liveness ==
  \E i \in Proc : []<> Crit(i)

=============================================================================