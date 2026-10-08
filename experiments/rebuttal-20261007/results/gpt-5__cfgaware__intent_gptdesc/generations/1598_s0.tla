---- MODULE FastMutex ----
EXTENDS Naturals

CONSTANT N

(*
  Lamport-style fast mutual exclusion protocol with spinning and back-off for N processes.
  Shared registers: X, Y; per-process intent flags: flag[i].
  Local control state pc[i] encodes where process i is in the entry protocol.
*)

VARIABLES pc, flag, X, Y

Proc == 1..N

PCSet ==
  {"Start", "AfterX", "WaitY0", "SetY", "CheckX",
   "WaitFlags", "CheckY2", "WaitY0b", "CS"}

TypeOK ==
  /\ pc \in [Proc -> PCSet]
  /\ flag \in [Proc -> BOOLEAN]
  /\ X \in 0..N
  /\ Y \in 0..N

Init ==
  /\ pc = [i \in Proc |-> "Start"]
  /\ flag = [i \in Proc |-> FALSE]
  /\ X = 0
  /\ Y = 0

(*
  Process i actions
  - StartToAfterX: declare intent and announce self in X
  - AfterX_SeeY0 / AfterX_SeeYNot0: branch on Y to either proceed or back off
  - WaitY0_ToStart / WaitY0b_ToStart: spin on Y=0 then retry
  - SetY: announce self in Y
  - CheckX_Equal / CheckX_NotEqual: fast path if X=i, else withdraw and wait
  - WaitFlags_AllFalse: spin until all other flags are false
  - CheckY2_Good / CheckY2_Bad: if still owning Y then enter CS, else back off
  - ExitCS: reset shared indicators and loop
*)

StartToAfterX(i) ==
  /\ pc[i] = "Start"
  /\ pc' = [pc EXCEPT ![i] = "AfterX"]
  /\ flag' = [flag EXCEPT ![i] = TRUE]
  /\ X' = i
  /\ UNCHANGED Y

AfterX_SeeY0(i) ==
  /\ pc[i] = "AfterX"
  /\ Y = 0
  /\ pc' = [pc EXCEPT ![i] = "SetY"]
  /\ UNCHANGED <<flag, X, Y>>

AfterX_SeeYNot0(i) ==
  /\ pc[i] = "AfterX"
  /\ Y # 0
  /\ pc' = [pc EXCEPT ![i] = "WaitY0"]
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<X, Y>>

WaitY0_ToStart(i) ==
  /\ pc[i] = "WaitY0"
  /\ Y = 0
  /\ pc' = [pc EXCEPT ![i] = "Start"]
  /\ UNCHANGED <<flag, X, Y>>

SetY(i) ==
  /\ pc[i] = "SetY"
  /\ Y' = i
  /\ pc' = [pc EXCEPT ![i] = "CheckX"]
  /\ UNCHANGED <<flag, X>>

CheckX_Equal(i) ==
  /\ pc[i] = "CheckX"
  /\ X = i
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ UNCHANGED <<flag, X, Y>>

CheckX_NotEqual(i) ==
  /\ pc[i] = "CheckX"
  /\ X # i
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "WaitFlags"]
  /\ UNCHANGED <<X, Y>>

WaitFlags_AllFalse(i) ==
  /\ pc[i] = "WaitFlags"
  /\ \A j \in Proc: (j = i) \/ (flag[j] = FALSE)
  /\ pc' = [pc EXCEPT ![i] = "CheckY2"]
  /\ UNCHANGED <<flag, X, Y>>

CheckY2_Good(i) ==
  /\ pc[i] = "CheckY2"
  /\ Y = i
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ UNCHANGED <<flag, X, Y>>

CheckY2_Bad(i) ==
  /\ pc[i] = "CheckY2"
  /\ Y # i
  /\ pc' = [pc EXCEPT ![i] = "WaitY0b"]
  /\ UNCHANGED <<flag, X, Y>>

WaitY0b_ToStart(i) ==
  /\ pc[i] = "WaitY0b"
  /\ Y = 0
  /\ pc' = [pc EXCEPT ![i] = "Start"]
  /\ UNCHANGED <<flag, X, Y>>

ExitCS(i) ==
  /\ pc[i] = "CS"
  /\ Y' = 0
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "Start"]
  /\ UNCHANGED X

Proc(i) ==
  StartToAfterX(i)
  \/ AfterX_SeeY0(i)
  \/ AfterX_SeeYNot0(i)
  \/ WaitY0_ToStart(i)
  \/ SetY(i)
  \/ CheckX_Equal(i)
  \/ CheckX_NotEqual(i)
  \/ WaitFlags_AllFalse(i)
  \/ CheckY2_Good(i)
  \/ CheckY2_Bad(i)
  \/ WaitY0b_ToStart(i)
  \/ ExitCS(i)

Next ==
  \E i \in Proc: Proc(i)

vars == << pc, flag, X, Y >>

(*
  Safety: mutual exclusion
*)
Mutex ==
  \A i \in Proc: \A j \in Proc:
    i # j => ~(pc[i] = "CS" /\ pc[j] = "CS")

Invariant == TypeOK /\ Mutex

(*
  System specification with per-process weak fairness
*)
Spec ==
  Init /\ [][Next]_vars /\ (\A i \in Proc: WF_vars(Proc(i)))

(*
  Liveness: system-wide starvation freedom
  Infinitely often, some process is in the critical section.
*)
Liveness ==
  []<>(\E i \in Proc: pc[i] = "CS")

====