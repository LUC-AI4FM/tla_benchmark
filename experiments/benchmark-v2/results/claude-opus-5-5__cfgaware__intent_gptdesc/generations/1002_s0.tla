---------------------------- MODULE BarrierSync ----------------------------
(***************************************************************************)
(* Abstract model of a reusable barrier for N identical processes.         *)
(*                                                                         *)
(* Each process cycles through three local phases:                         *)
(*   "running"  : doing pre-barrier work for the current round             *)
(*   "arrived"  : has signalled arrival and is blocked at the barrier      *)
(*   "released" : the barrier has opened for its round; it may proceed     *)
(*                                                                         *)
(* Round bookkeeping uses a 1-bit generation counter, as in a              *)
(* sense-reversing barrier, so the state space stays finite.               *)
(*   round      : shared generation bit (0..1)                             *)
(*   myRound[p] : generation that process p is participating in            *)
(*   count      : number of processes that have arrived in this round      *)
(*                                                                         *)
(* Assumptions:                                                            *)
(*   - N is a finite natural number with N > 0.                            *)
(*   - Steps are reliable and atomic. There are no crashes and no lost     *)
(*     signals.                                                            *)
(*   - The release of all processes is one atomic step (Release).          *)
(*                                                                         *)
(* Fairness:                                                               *)
(*   Weak fairness is enough for liveness. Every action, once enabled,     *)
(*   stays enabled until it is taken:                                      *)
(*   - Release stays enabled while all processes have arrived.             *)
(*   - Proceed(p) stays enabled while p is released.                       *)
(*   - Arrive(p) stays enabled while p is running.                         *)
(*   So WF on each action is sufficient, and strong fairness is not        *)
(*   needed. WF on Arrive(p) is the assumption that processes do not stay  *)
(*   in their work phase forever. Without it, liveness holds only in the   *)
(*   conditional form "all arrive ~> all released".                        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N > 0

Procs  == 1..N
Phases == {"running", "arrived", "released"}

VARIABLES phase, myRound, round, count

vars == <<phase, myRound, round, count>>

-----------------------------------------------------------------------------
TypeOK ==
    /\ phase   \in [Procs -> Phases]
    /\ myRound \in [Procs -> 0..1]
    /\ round   \in 0..1
    /\ count   \in 0..N

Init ==
    /\ phase   = [p \in Procs |-> "running"]
    /\ myRound = [p \in Procs |-> 0]
    /\ round   = 0
    /\ count   = 0

(* Process p reaches the barrier and signals arrival for its round. *)
Arrive(p) ==
    /\ phase[p] = "running"
    /\ myRound[p] = round
    /\ phase' = [phase EXCEPT ![p] = "arrived"]
    /\ count' = count + 1
    /\ UNCHANGED <<myRound, round>>

(* Once all N processes have arrived, the barrier opens atomically.       *)
(* It flips the generation bit and resets the arrival counter so it can   *)
(* be reused.                                                             *)
Release ==
    /\ count = N
    /\ \A p \in Procs : phase[p] = "arrived"
    /\ phase' = [p \in Procs |-> "released"]
    /\ round' = 1 - round
    /\ count' = 0
    /\ UNCHANGED myRound

(* A released process leaves the barrier and joins the next round. *)
Proceed(p) ==
    /\ phase[p] = "released"
    /\ phase'   = [phase EXCEPT ![p] = "running"]
    /\ myRound' = [myRound EXCEPT ![p] = round]
    /\ UNCHANGED <<round, count>>

Next ==
    \/ \E p \in Procs : Arrive(p)
    \/ Release
    \/ \E p \in Procs : Proceed(p)

Fairness ==
    /\ WF_vars(Release)
    /\ \A p \in Procs : WF_vars(Arrive(p))
    /\ \A p \in Procs : WF_vars(Proceed(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Helper predicates *)
AllArrived  == \A p \in Procs : phase[p] = "arrived"
AllReleased == \A p \in Procs : phase[p] = "released"
SomeReleased == \E p \in Procs : phase[p] = "released"

(***************************************************************************)
(* Safety and reusability (state invariant).                               *)
(*                                                                         *)
(* 1. count is exactly the number of processes that have arrived in the   *)
(*    current generation, so arrivals never leak across rounds.            *)
(* 2. A process is released only if every process arrived for that round. *)
(*    While any process is still "released" (old generation 1 - round),   *)
(*    every non-released process has passed through that barrier and is   *)
(*    now in the new generation. No process is still in its pre-barrier   *)
(*    work for the round that was released.                                *)
(* 3. Released processes belong to the previous generation, so rounds are  *)
(*    never confused.                                                      *)
(* 4. No process is released while count shows a partially filled round   *)
(*    of its own generation.                                               *)
(***************************************************************************)
BarrierProperty ==
    /\ count = Cardinality({p \in Procs : phase[p] = "arrived"})
    /\ \A p \in Procs : phase[p] \in {"running", "arrived"} => myRound[p] = round
    /\ \A p \in Procs : phase[p] = "released" => myRound[p] = 1 - round
    /\ SomeReleased =>
          \A q \in Procs : phase[q] = "released" \/ myRound[q] = round
    /\ count = N => AllArrived

(* Safety at the action level: Release can fire only when every process   *)
(* has arrived.                                                           *)
ReleaseSafety ==
    [][ (\E p \in Procs : phase[p] /= "released" /\ phase'[p] = "released")
          => AllArrived ]_vars

(* Liveness: if all processes arrive, they are all eventually released.   *)
Liveness == AllArrived ~> AllReleased

(* Progress and reusability: every released process eventually resumes,  *)
(* and the barrier keeps completing rounds forever.                      *)
ProcessProgress == \A p \in Procs : (phase[p] = "released") ~> (phase[p] = "running")
RoundsRepeat    == []<>AllReleased

THEOREM Spec => [](TypeOK /\ BarrierProperty)
THEOREM Spec => ReleaseSafety /\ Liveness /\ ProcessProgress /\ RoundsRepeat
=============================================================================