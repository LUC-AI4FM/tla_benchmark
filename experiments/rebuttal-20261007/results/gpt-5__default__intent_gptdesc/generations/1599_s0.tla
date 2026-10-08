------------------------------ MODULE FastFastLock ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

(*
  A fast mutual-exclusion lock for N identical processes using only atomic
  read/write registers. The algorithm provides a fast path (Lamport’s fast
  mutual exclusion) when there is no contention and a starvation-free slow
  path (Filter lock) when there is contention. Fast and slow paths are
  coordinated so they cannot overlap in the critical section.

  Safety:
    - Mutual exclusion: at most one process is in the critical section.

  Liveness:
    - No deadlock under contention: if some process is trying to enter, then
      eventually some process enters the critical section.
    - Starvation freedom under weak fairness (of process steps): any process
      that repeatedly attempts to enter will enter the critical section
      infinitely often.

  Resources:
    - Per-process bounded local/shared scalars: each process uses a constant
      number of booleans/integers; shared state includes arrays indexed by
      process id and a constant number of scalars (x, y).
*)

(***************************************************************************)
(* State space                                                             *)
(***************************************************************************)

Proc == 1..N

LevelMax == IF N > 1 THEN N - 1 ELSE 1
Levels   == 1..LevelMax

PCStates ==
  {"NCS",            \* noncritical section
   "CheckY",         \* fast path: after setting b[i] and x := i, check y
   "SetY",           \* fast path: set y := i
   "CheckX",         \* fast path: check x = i
   "WaitB",          \* fast path degrade: wait until all other b[j] = FALSE
   "WaitY0ForSlow",  \* fast path degrade: then wait y = 0 before slow path
   "CheckNoSlow",    \* fast path: ensure no slow-path activity
   "SlowStart",      \* begin slow (Filter) path
   "FilterWait",     \* waiting inside Filter levels
   "CS_F",           \* in critical section via fast path
   "CS_S"}           \* in critical section via slow (Filter) path

VARIABLES
  pc,     \* [Proc -> PCStates]
  b,      \* [Proc -> BOOLEAN]  -- fast-path intent flags
  x,      \* in Proc \cup {0}   -- fast-path doorway 1
  y,      \* in Proc \cup {0}   -- fast-path doorway 2 (nonzero while fast-CS occupied)
  level,  \* [Proc -> 0..LevelMax]  -- Filter level per process
  victim  \* [Levels -> Proc \cup {0}] -- Filter victim per level

vars == << pc, b, x, y, level, victim >>

(***************************************************************************)
(* Helper predicates                                                       *)
(***************************************************************************)

InCS(i) == pc[i] = "CS_F" \/ pc[i] = "CS_S"

Attempting(i) == pc[i] # "NCS"

SomeoneTrying == \E i \in Proc: Attempting(i)

SomeInCS == \E i \in Proc: InCS(i)

NoOtherB(i) == \A j \in Proc: j = i \/ ~b[j]

NoSlowActive == \A k \in Proc: level[k] = 0

FilterGuard(i, l) ==
  \A k \in Proc:
    (k = i) \/ (level[k] < l) \/ (victim[l] # i)

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)

Init ==
  /\ pc = [i \in Proc |-> "NCS"]
  /\ b  = [i \in Proc |-> FALSE]
  /\ x = 0
  /\ y = 0
  /\ level = [i \in Proc |-> 0]
  /\ victim = [l \in Levels |-> 0]

(***************************************************************************)
(* Process i step transitions                                              *)
(***************************************************************************)

NCS_to_CheckY(i) ==
  /\ pc[i] = "NCS"
  /\ pc' = [pc EXCEPT ![i] = "CheckY"]
  /\ b'  = [b  EXCEPT ![i] = TRUE]
  /\ x' = i
  /\ UNCHANGED << y, level, victim >>

CheckY_to_SetY(i) ==
  /\ pc[i] = "CheckY"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "SetY"]
  /\ UNCHANGED << b, x, y, level, victim >>

CheckY_to_Degrade_NoY(i) ==
  /\ pc[i] = "CheckY"
  /\ y # 0
  /\ pc' = [pc EXCEPT ![i] = "SlowStart"]
  /\ b'  = [b  EXCEPT ![i] = FALSE]
  /\ UNCHANGED << x, y, level, victim >>

SetY_to_CheckX(i) ==
  /\ pc[i] = "SetY"
  /\ pc' = [pc EXCEPT ![i] = "CheckX"]
  /\ y' = i
  /\ UNCHANGED << b, x, level, victim >>

CheckX_to_CheckNoSlow(i) ==
  /\ pc[i] = "CheckX"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "CheckNoSlow"]
  /\ UNCHANGED << b, x, y, level, victim >>

CheckX_to_WaitB(i) ==
  /\ pc[i] = "CheckX"
  /\ x # i
  /\ pc' = [pc EXCEPT ![i] = "WaitB"]
  /\ b'  = [b  EXCEPT ![i] = FALSE]
  /\ UNCHANGED << x, y, level, victim >>

WaitB_to_SlowStart(i) ==
  /\ pc[i] = "WaitB"
  /\ NoOtherB(i)
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "SlowStart"]
  /\ UNCHANGED << b, x, y, level, victim >>

WaitB_to_WaitY0ForSlow(i) ==
  /\ pc[i] = "WaitB"
  /\ NoOtherB(i)
  /\ y # 0
  /\ pc' = [pc EXCEPT ![i] = "WaitY0ForSlow"]
  /\ UNCHANGED << b, x, y, level, victim >>

WaitY0ForSlow_to_SlowStart(i) ==
  /\ pc[i] = "WaitY0ForSlow"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "SlowStart"]
  /\ UNCHANGED << b, x, y, level, victim >>

CheckNoSlow_to_CSEnterFast(i) ==
  /\ pc[i] = "CheckNoSlow"
  /\ NoSlowActive
  /\ pc' = [pc EXCEPT ![i] = "CS_F"]
  /\ UNCHANGED << b, x, y, level, victim >>

CheckNoSlow_to_DegradeFromFast(i) ==
  /\ pc[i] = "CheckNoSlow"
  /\ ~NoSlowActive
  /\ pc' = [pc EXCEPT ![i] = "SlowStart"]
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ UNCHANGED << x, level, victim >>

SlowStart_to_FilterLevel1(i) ==
  /\ pc[i] = "SlowStart"
  /\ pc' = [pc EXCEPT ![i] = "FilterWait"]
  /\ level' = [level EXCEPT ![i] = 1]
  /\ victim' = [victim EXCEPT ![1] = i]
  /\ UNCHANGED << b, x, y >>

FilterWait_Advance(i) ==
  /\ pc[i] = "FilterWait"
  /\ LET l == level[i] IN
       /\ l \in Levels
       /\ l < LevelMax
       /\ FilterGuard(i, l)
       /\ level'  = [level  EXCEPT ![i] = l + 1]
       /\ victim' = [victim EXCEPT ![l + 1] = i]
       /\ pc' = pc
       /\ UNCHANGED << b, x, y >>

FilterWait_to_CSSlow(i) ==
  /\ pc[i] = "FilterWait"
  /\ LET l == level[i] IN
       /\ l = LevelMax
       /\ FilterGuard(i, l)
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "CS_S"]
  /\ UNCHANGED << b, x, y, level, victim >>

ExitCS_F(i) ==
  /\ pc[i] = "CS_F"
  /\ pc' = [pc EXCEPT ![i] = "NCS"]
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ UNCHANGED << x, level, victim >>

ExitCS_S(i) ==
  /\ pc[i] = "CS_S"
  /\ pc' = [pc EXCEPT ![i] = "NCS"]
  /\ level' = [level EXCEPT ![i] = 0]
  /\ UNCHANGED << b, x, y, victim >>

ProcStep(i) ==
  NCS_to_CheckY(i)
  \/ CheckY_to_SetY(i)
  \/ CheckY_to_Degrade_NoY(i)
  \/ SetY_to_CheckX(i)
  \/ CheckX_to_CheckNoSlow(i)
  \/ CheckX_to_WaitB(i)
  \/ WaitB_to_SlowStart(i)
  \/ WaitB_to_WaitY0ForSlow(i)
  \/ WaitY0ForSlow_to_SlowStart(i)
  \/ CheckNoSlow_to_CSEnterFast(i)
  \/ CheckNoSlow_to_DegradeFromFast(i)
  \/ SlowStart_to_FilterLevel1(i)
  \/ FilterWait_Advance(i)
  \/ FilterWait_to_CSSlow(i)
  \/ ExitCS_F(i)
  \/ ExitCS_S(i)

Next == \E i \in Proc: ProcStep(i)

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeOK ==
  /\ pc \in [Proc -> PCStates]
  /\ b \in [Proc -> BOOLEAN]
  /\ x \in Proc \cup {0}
  /\ y \in Proc \cup {0}
  /\ level \in [Proc -> 0..LevelMax]
  /\ victim \in [Levels -> (Proc \cup {0})]

MutualExclusion ==
  \A i, j \in Proc:
    (i # j) => ~(InCS(i) /\ InCS(j))

Inv == TypeOK /\ MutualExclusion

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

NoDeadlockWhenContention ==
  [] (SomeoneTrying => <> SomeInCS)

FairStarvationFree ==
  \A i \in Proc: ([] <> Attempting(i)) => ([] <> InCS(i))

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Proc: WF_vars(ProcStep(i))

=============================================================================