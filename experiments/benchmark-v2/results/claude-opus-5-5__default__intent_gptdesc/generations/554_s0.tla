------------------------------- MODULE FilterLock -------------------------------
(***************************************************************************)
(* The Filter lock: Peterson's mutual-exclusion algorithm generalized to N *)
(* processes.                                                              *)
(*                                                                         *)
(* There are N-1 levels, numbered 1..N-1. To enter the critical section a  *)
(* process must pass every level in order. At each level L it does three   *)
(* steps:                                                                  *)
(*   1. it announces level[p] := L;                                        *)
(*   2. it makes itself the last entrant at that level, victim[L] := p;    *)
(*   3. it spins while some other process is at level >= L and it is      *)
(*      still the victim at L.                                             *)
(* At most N-L processes can pass level L, so at most one process reaches  *)
(* the critical section. On exit a process resets its level to 0.          *)
(*                                                                         *)
(* Every step reads or writes at most one single-writer per-process level  *)
(* variable or one victim variable. The only exception is the spin test,   *)
(* which is modeled as one atomic guard.                                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

Procs  == 1..N
Levels == 1..(N-1)

VARIABLES
    pc,      \* pc[p]     : control location of process p
    level,   \* level[p]  : shared level indicator of p (0 = not competing)
    victim,  \* victim[L] : last process to enter level L
    lv       \* lv[p]     : level p is currently trying to pass (private)

vars == << pc, level, victim, lv >>

Locations == {"ncs", "setlevel", "setvictim", "wait", "cs", "exit"}
Trying    == {"setlevel", "setvictim", "wait"}

TypeOK ==
    /\ pc     \in [Procs -> Locations]
    /\ level  \in [Procs -> 0..(N-1)]
    /\ victim \in [Levels -> Procs]
    /\ lv     \in [Procs -> 0..N]

Init ==
    /\ pc     = [p \in Procs  |-> "ncs"]
    /\ level  = [p \in Procs  |-> 0]
    /\ victim = [l \in Levels |-> 1]
    /\ lv     = [p \in Procs  |-> 0]

-----------------------------------------------------------------------------
(* Leave the noncritical section and start the entry protocol. A process  *)
(* may also stay in its noncritical section forever.                       *)
TryEnter(p) ==
    /\ pc[p] = "ncs"
    /\ IF N = 1
         THEN pc' = [pc EXCEPT ![p] = "cs"]
         ELSE pc' = [pc EXCEPT ![p] = "setlevel"]
    /\ lv' = [lv EXCEPT ![p] = 1]
    /\ UNCHANGED << level, victim >>

(* Announce the level being attempted. *)
SetLevel(p) ==
    /\ pc[p] = "setlevel"
    /\ level' = [level EXCEPT ![p] = lv[p]]
    /\ pc'    = [pc EXCEPT ![p] = "setvictim"]
    /\ UNCHANGED << victim, lv >>

(* Become the last entrant (victim) at this level. *)
SetVictim(p) ==
    /\ pc[p] = "setvictim"
    /\ victim' = [victim EXCEPT ![lv[p]] = p]
    /\ pc'     = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED << level, lv >>

Blocked(p) ==
    /\ \E k \in Procs \ {p} : level[k] >= lv[p]
    /\ victim[lv[p]] = p

(* Spin-wait: the step is enabled only when p is no longer blocked. While *)
(* blocked, p busy-waits, which leaves the state unchanged.                *)
Wait(p) ==
    /\ pc[p] = "wait"
    /\ ~Blocked(p)
    /\ IF lv[p] = N - 1
         THEN /\ pc' = [pc EXCEPT ![p] = "cs"]
              /\ UNCHANGED lv
         ELSE /\ pc' = [pc EXCEPT ![p] = "setlevel"]
              /\ lv' = [lv EXCEPT ![p] = lv[p] + 1]
    /\ UNCHANGED << level, victim >>

(* Leave the critical section. *)
LeaveCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED << level, victim, lv >>

(* Exit protocol: give up access by resetting the level. *)
ExitProto(p) ==
    /\ pc[p] = "exit"
    /\ level' = [level EXCEPT ![p] = 0]
    /\ lv'    = [lv EXCEPT ![p] = 0]
    /\ pc'    = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED victim

(* All steps of p except leaving the noncritical section, which is optional. *)
ProtocolStep(p) ==
    \/ SetLevel(p)
    \/ SetVictim(p)
    \/ Wait(p)
    \/ LeaveCS(p)
    \/ ExitProto(p)

Proc(p) == TryEnter(p) \/ ProtocolStep(p)

Next == \E p \in Procs : Proc(p)

(***************************************************************************)
(* Fairness assumptions.                                                   *)
(*   - Weak fairness on every protocol step of every process. A process    *)
(*     never halts in its entry protocol, critical section or exit         *)
(*     protocol, but it may stay in its noncritical section forever.       *)
(*   - Strong fairness on the spin-wait exit. A waiting process that is    *)
(*     unblocked infinitely often eventually takes the step, even if other *)
(*     processes' level writes make its guard fluctuate.                   *)
(***************************************************************************)
Fairness ==
    \A p \in Procs :
        /\ WF_vars(ProtocolStep(p))
        /\ SF_vars(Wait(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(*                          Safety properties                             *)

InCS(p) == pc[p] = "cs"

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(InCS(p) /\ InCS(q))

(* p has passed level L: it is trying a higher level, or it is in the  *)
(* critical section or the exit protocol.                               *)
Passed(p, L) ==
    \/ pc[p] \in Trying /\ lv[p] > L
    \/ pc[p] \in {"cs", "exit"}

(* Filter invariant: at most N-L processes have passed level L. *)
FilterInvariant ==
    \A L \in Levels : Cardinality({p \in Procs : Passed(p, L)}) <= N - L

(* Consistency between the shared level indicator and the private level. *)
LevelConsistent ==
    \A p \in Procs :
        /\ pc[p] = "ncs" => level[p] = 0
        /\ pc[p] \in {"setvictim", "wait"} => level[p] = lv[p]
        /\ pc[p] = "setlevel" => level[p] = lv[p] - 1

-----------------------------------------------------------------------------
(*                         Liveness properties                            *)

(* Deadlock freedom: if some process is trying, some process gets in. *)
DeadlockFreedom ==
    (\E p \in Procs : pc[p] \in Trying) ~> (\E p \in Procs : InCS(p))

(* Starvation freedom: every process that tries eventually gets in. *)
StarvationFreedom ==
    \A p \in Procs : (pc[p] \in Trying) ~> InCS(p)

(* Every process in the critical section eventually returns to its     *)
(* noncritical section.                                                 *)
ExitProgress ==
    \A p \in Procs : InCS(p) ~> (pc[p] = "ncs")

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ MutualExclusion /\ FilterInvariant /\ LevelConsistent)
THEOREM Spec => DeadlockFreedom /\ StarvationFreedom /\ ExitProgress
=============================================================================