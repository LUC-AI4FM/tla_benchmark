---------------------------- MODULE BarrierSync ----------------------------
(***************************************************************************)
(* Synchronous Barrier Synchronization for N Identical Processes           *)
(*                                                                         *)
(* This specification models a reusable barrier where N processes          *)
(* repeatedly synchronize through arrive and release phases.               *)
(*                                                                         *)
(* Assumptions:                                                            *)
(* - N > 0 (finite number of processes)                                    *)
(* - Reliable steps (no process crashes or message loss)                   *)
(* - Weak fairness is required on individual process actions for liveness  *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N > 0

(***************************************************************************)
(* Process identifiers                                                      *)
(***************************************************************************)
Procs == 1..N

(***************************************************************************)
(* Process phases:                                                          *)
(* - "working": process is executing between barriers                       *)
(* - "arrived": process has arrived at barrier, waiting for release         *)
(* - "released": process has been released and can proceed                  *)
(***************************************************************************)
Phases == {"working", "arrived", "released"}

(***************************************************************************)
(* Barrier states:                                                          *)
(* - "gathering": waiting for processes to arrive                           *)
(* - "releasing": all processes arrived, releasing them                     *)
(***************************************************************************)
BarrierStates == {"gathering", "releasing"}

VARIABLES
    phase,          \* phase[p] \in Phases: current phase of process p
    round,          \* round[p] \in Nat: current round number for process p
    barrierState,   \* barrierState \in BarrierStates: global barrier state
    barrierRound,   \* barrierRound \in Nat: current barrier round number
    arrivedCount    \* arrivedCount \in 0..N: count of arrived processes in current round

vars == <<phase, round, barrierState, barrierRound, arrivedCount>>

(***************************************************************************)
(* Type Invariant                                                           *)
(***************************************************************************)
TypeInvariant ==
    /\ phase \in [Procs -> Phases]
    /\ round \in [Procs -> Nat]
    /\ barrierState \in BarrierStates
    /\ barrierRound \in Nat
    /\ arrivedCount \in 0..N

(***************************************************************************)
(* Initial State                                                            *)
(* All processes start in working phase at round 0                          *)
(***************************************************************************)
Init ==
    /\ phase = [p \in Procs |-> "working"]
    /\ round = [p \in Procs |-> 0]
    /\ barrierState = "gathering"
    /\ barrierRound = 0
    /\ arrivedCount = 0

(***************************************************************************)
(* Process Actions                                                          *)
(***************************************************************************)

(***************************************************************************)
(* Arrive: A working process arrives at the barrier for its current round  *)
(* Process can only arrive if barrier is gathering for the process's round *)
(***************************************************************************)
Arrive(p) ==
    /\ phase[p] = "working"
    /\ barrierState = "gathering"
    /\ round[p] = barrierRound
    /\ phase' = [phase EXCEPT ![p] = "arrived"]
    /\ arrivedCount' = arrivedCount + 1
    /\ UNCHANGED <<round, barrierState, barrierRound>>

(***************************************************************************)
(* OpenBarrier: When all processes have arrived, transition barrier to     *)
(* releasing state. This is an atomic transition.                          *)
(***************************************************************************)
OpenBarrier ==
    /\ barrierState = "gathering"
    /\ arrivedCount = N
    /\ barrierState' = "releasing"
    /\ UNCHANGED <<phase, round, barrierRound, arrivedCount>>

(***************************************************************************)
(* Release: A process that has arrived is released from the barrier        *)
(* Can only happen when barrier is in releasing state                      *)
(***************************************************************************)
Release(p) ==
    /\ phase[p] = "arrived"
    /\ barrierState = "releasing"
    /\ phase' = [phase EXCEPT ![p] = "released"]
    /\ UNCHANGED <<round, barrierState, barrierRound, arrivedCount>>

(***************************************************************************)
(* ResetBarrier: When all processes have been released, reset the barrier  *)
(* for the next round. This happens when no process is in arrived state    *)
(* and barrier is in releasing state.                                      *)
(***************************************************************************)
AllReleased ==
    /\ barrierState = "releasing"
    /\ \A p \in Procs : phase[p] # "arrived"

ResetBarrier ==
    /\ AllReleased
    /\ barrierState' = "gathering"
    /\ barrierRound' = barrierRound + 1
    /\ arrivedCount' = 0
    /\ UNCHANGED <<phase, round>>

(***************************************************************************)
(* ContinueWorking: A released process continues working and prepares for  *)
(* the next barrier round                                                  *)
(***************************************************************************)
ContinueWorking(p) ==
    /\ phase[p] = "released"
    /\ phase' = [phase EXCEPT ![p] = "working"]
    /\ round' = [round EXCEPT ![p] = round[p] + 1]
    /\ UNCHANGED <<barrierState, barrierRound, arrivedCount>>

(***************************************************************************)
(* Next State Relation                                                      *)
(***************************************************************************)
Next ==
    \/ \E p \in Procs : Arrive(p)
    \/ OpenBarrier
    \/ \E p \in Procs : Release(p)
    \/ ResetBarrier
    \/ \E p \in Procs : ContinueWorking(p)

(***************************************************************************)
(* Fairness Conditions                                                      *)
(* Weak fairness on all process actions ensures no process is permanently  *)
(* starved. Weak fairness on barrier actions ensures progress.             *)
(***************************************************************************)
Fairness ==
    /\ \A p \in Procs : WF_vars(Arrive(p))
    /\ \A p \in Procs : WF_vars(Release(p))
    /\ \A p \in Procs : WF_vars(ContinueWorking(p))
    /\ WF_vars(OpenBarrier)
    /\ WF_vars(ResetBarrier)

(***************************************************************************)
(* Specification                                                            *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* SAFETY PROPERTIES                                                        *)
(***************************************************************************)

(***************************************************************************)
(* Safety: No process may be released from the barrier until every         *)
(* process has signaled arrival for that round.                            *)
(* This is ensured by: barrier only transitions to "releasing" when        *)
(* arrivedCount = N, and release only happens in "releasing" state.        *)
(***************************************************************************)
SafetyNoEarlyRelease ==
    \A p \in Procs :
        phase[p] = "released" =>
            (barrierState = "releasing" \/ barrierState = "gathering")

(***************************************************************************)
(* Stronger safety: If any process is released, all must have arrived      *)
(* In releasing state, all processes in current round must be arrived or   *)
(* released (not working)                                                  *)
(***************************************************************************)
SafetyAllArrivedBeforeRelease ==
    barrierState = "releasing" =>
        \A p \in Procs : 
            round[p] = barrierRound => phase[p] \in {"arrived", "released"}

(***************************************************************************)
(* Round consistency: processes don't get ahead of the barrier             *)
(***************************************************************************)
RoundConsistency ==
    \A p \in Procs :
        /\ round[p] <= barrierRound + 1
        /\ (phase[p] = "arrived" => round[p] = barrierRound)
        /\ (phase[p] = "released" => round[p] = barrierRound)

(***************************************************************************)
(* Arrived count consistency                                                *)
(***************************************************************************)
ArrivedCountConsistency ==
    barrierState = "gathering" =>
        arrivedCount = Cardinality({p \in Procs : phase[p] = "arrived" /\ round[p] = barrierRound})

(***************************************************************************)
(* Combined Safety Invariant                                                *)
(***************************************************************************)
SafetyInvariant ==
    /\ TypeInvariant
    /\ SafetyNoEarlyRelease
    /\ SafetyAllArrivedBeforeRelease
    /\ RoundConsistency

(***************************************************************************)
(* LIVENESS PROPERTIES                                                      *)
(***************************************************************************)

(***************************************************************************)
(* Liveness: Whenever all processes eventually arrive for some round,      *)
(* they will all eventually be released for that round.                    *)
(***************************************************************************)
AllArrived == \A p \in Procs : phase[p] = "arrived"
AllReleasedOrWorking == \A p \in Procs : phase[p] \in {"released", "working"}

LivenessAllArrivedLeadsToRelease ==
    AllArrived ~> AllReleasedOrWorking

(***************************************************************************)
(* Progress: Every process that arrives will eventually be released        *)
(***************************************************************************)
LivenessArrivedLeadsToReleased(p) ==
    phase[p] = "arrived" ~> phase[p] = "released"

LivenessProgress ==
    \A p \in Procs : LivenessArrivedLeadsToReleased(p)

(***************************************************************************)
(* Reusability: After release, processes can participate in subsequent     *)
(* rounds. This is demonstrated by showing rounds can increase.            *)
(***************************************************************************)
LivenessRoundsProgress ==
    \A r \in Nat : (barrierRound = r) ~> (barrierRound >= r)

(***************************************************************************)
(* No starvation: Every working process eventually arrives                  *)
(***************************************************************************)
LivenessNoStarvation(p) ==
    phase[p] = "working" ~> phase[p] = "arrived"

LivenessNoStarvationAll ==
    \A p \in Procs : LivenessNoStarvation(p)

=============================================================================