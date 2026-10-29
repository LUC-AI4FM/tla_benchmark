------------------------------- MODULE MutexFilter -------------------------------
(***************************************************************************)
(* An N-process mutual-exclusion model.                                    *)
(*                                                                         *)
(* Each process cycles through four phases:                                *)
(*   noncritical -> entry protocol -> critical section -> exit protocol.   *)
(*                                                                         *)
(* The entry protocol shown here is the generalized Peterson ("filter")    *)
(* protocol. It is one concrete instance used so that the model can be     *)
(* checked. The safety and liveness properties at the end of the module    *)
(* are stated purely in terms of the per-process control state `pc`, so   *)
(* they do not depend on the chosen protocol.                              *)
(*                                                                         *)
(* Shared synchronization state:                                           *)
(*   level[p]  : the level process p currently occupies (0 = not          *)
(*               competing).                                               *)
(*   victim[l] : the last process to arrive at level l.                    *)
(*                                                                         *)
(* Local state:                                                            *)
(*   pc[p]     : the control location of process p.                       *)
(*   curLvl[p] : the level process p is currently trying to pass.         *)
(*                                                                         *)
(* Atomicity assumptions: each labelled step below is atomic. The wait    *)
(* step reads every other process's level in one atomic step.             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 1

Procs  == 1..N
Levels == 1..(N-1)

VARIABLES pc, level, victim, curLvl

vars == <<pc, level, victim, curLvl>>

\* Control locations.
\*   "ncs"      : noncritical section
\*   "setLevel" : entry protocol, announce the current level
\*   "setVictim": entry protocol, become the victim at the current level
\*   "wait"     : entry protocol, wait to pass the current level
\*   "cs"       : critical section
\*   "exit"     : exit protocol
PCs    == {"ncs", "setLevel", "setVictim", "wait", "cs", "exit"}
Trying == {"setLevel", "setVictim", "wait"}

-----------------------------------------------------------------------------
TypeOK ==
    /\ pc     \in [Procs -> PCs]
    /\ level  \in [Procs -> 0..(N-1)]
    /\ victim \in [Levels -> Procs]
    /\ curLvl \in [Procs -> 0..(N-1)]

Init ==
    /\ pc     = [p \in Procs |-> "ncs"]
    /\ level  = [p \in Procs |-> 0]
    /\ victim \in [Levels -> Procs]
    /\ curLvl = [p \in Procs |-> 0]

-----------------------------------------------------------------------------
(* Process actions *)

\* Leave the noncritical section and start the entry protocol. A process
\* may also stay in its noncritical section forever, so this action has
\* no fairness requirement.
Try(p) ==
    /\ pc[p] = "ncs"
    /\ IF N = 1
         THEN /\ pc'     = [pc EXCEPT ![p] = "cs"]
              /\ curLvl' = curLvl
         ELSE /\ pc'     = [pc EXCEPT ![p] = "setLevel"]
              /\ curLvl' = [curLvl EXCEPT ![p] = 1]
    /\ UNCHANGED <<level, victim>>

SetLevel(p) ==
    /\ pc[p] = "setLevel"
    /\ level' = [level EXCEPT ![p] = curLvl[p]]
    /\ pc'    = [pc EXCEPT ![p] = "setVictim"]
    /\ UNCHANGED <<victim, curLvl>>

SetVictim(p) ==
    /\ pc[p] = "setVictim"
    /\ victim' = [victim EXCEPT ![curLvl[p]] = p]
    /\ pc'     = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED <<level, curLvl>>

CanPass(p) ==
    \/ \A q \in Procs \ {p} : level[q] < curLvl[p]
    \/ victim[curLvl[p]] # p

Wait(p) ==
    /\ pc[p] = "wait"
    /\ CanPass(p)
    /\ IF curLvl[p] = N - 1
         THEN /\ pc'     = [pc EXCEPT ![p] = "cs"]
              /\ curLvl' = curLvl
         ELSE /\ pc'     = [pc EXCEPT ![p] = "setLevel"]
              /\ curLvl' = [curLvl EXCEPT ![p] = curLvl[p] + 1]
    /\ UNCHANGED <<level, victim>>

\* Leave the critical section and begin the exit protocol.
LeaveCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<level, victim, curLvl>>

\* Exit protocol: release the claim and return to the noncritical section.
Exit(p) ==
    /\ pc[p] = "exit"
    /\ level'  = [level EXCEPT ![p] = 0]
    /\ curLvl' = [curLvl EXCEPT ![p] = 0]
    /\ pc'     = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED victim

Proc(p) ==
    \/ Try(p)
    \/ SetLevel(p)
    \/ SetVictim(p)
    \/ Wait(p)
    \/ LeaveCS(p)
    \/ Exit(p)

Next == \E p \in Procs : Proc(p)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Fairness assumptions required for the liveness claims.                  *)
(*                                                                         *)
(*  - Try(p) has NO fairness. A process may stay in its noncritical        *)
(*    section forever.                                                     *)
(*  - The entry and exit steps SetLevel, SetVictim and Exit, and the step  *)
(*    LeaveCS, have WEAK fairness. Once enabled, they stay enabled until   *)
(*    taken. LeaveCS being weakly fair means no process stays in its       *)
(*    critical section forever.                                            *)
(*  - The waiting step Wait(p) has STRONG fairness. Its guard depends on   *)
(*    other processes' levels, which can flicker, so it may be enabled     *)
(*    only intermittently. Strong fairness guarantees the step is taken    *)
(*    if it is enabled infinitely often.                                   *)
(*                                                                         *)
(* Safety does not depend on any fairness assumption.                      *)
(***************************************************************************)
Fairness ==
    \A p \in Procs :
        /\ WF_vars(SetLevel(p))
        /\ WF_vars(SetVictim(p))
        /\ SF_vars(Wait(p))
        /\ WF_vars(LeaveCS(p))
        /\ WF_vars(Exit(p))

SafetySpec == Init /\ [][Next]_vars

Spec == SafetySpec /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

AtMostOneInCS ==
    Cardinality({p \in Procs : pc[p] = "cs"}) <= 1

\* Consistency of the shared and local state with the control state.
StateConsistency ==
    \A p \in Procs :
        /\ (pc[p] = "ncs") => (level[p] = 0 /\ curLvl[p] = 0)
        /\ (pc[p] \in Trying) => (curLvl[p] \in Levels)

-----------------------------------------------------------------------------
(* Liveness. These properties hold under Spec, that is, under Fairness. *)

\* No starvation: every process that starts the entry protocol eventually
\* enters its critical section.
StarvationFreedom ==
    \A p \in Procs : (pc[p] \in Trying) ~> (pc[p] = "cs")

\* No deadlock: if some process is trying, then some process eventually
\* enters the critical section.
DeadlockFreedom ==
    (\E p \in Procs : pc[p] \in Trying) ~> (\E p \in Procs : pc[p] = "cs")

\* Every process in the critical section eventually leaves it and returns
\* to the noncritical section.
ExitProgress ==
    \A p \in Procs : (pc[p] \in {"cs", "exit"}) ~> (pc[p] = "ncs")

-----------------------------------------------------------------------------
THEOREM SafetySpec => [](TypeOK /\ MutualExclusion /\ AtMostOneInCS /\ StateConsistency)
THEOREM Spec => (StarvationFreedom /\ DeadlockFreedom /\ ExitProgress)
=============================================================================