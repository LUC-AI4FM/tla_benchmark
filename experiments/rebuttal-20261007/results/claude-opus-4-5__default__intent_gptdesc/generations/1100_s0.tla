-------------------------------- MODULE MutualExclusion --------------------------------
(***************************************************************************)
(* Abstract specification of mutual exclusion for concurrent processes.    *)
(* Processes cycle through: NonCritical -> Trying -> Critical -> Releasing *)
(* A binary lock coordinates access to the critical section.               *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS Procs  \* The set of process identifiers (at least two)

ASSUME ProcAssumption == /\ Procs # {}
                         /\ Cardinality(Procs) >= 2
                         /\ IsFiniteSet(Procs)

VARIABLES
    lock,   \* The state of the lock: "unlocked" or "locked"
    pc      \* Program counter: maps each process to its control state

vars == <<lock, pc>>

(***************************************************************************)
(* Type Definitions                                                        *)
(***************************************************************************)

LockStates == {"unlocked", "locked"}
PCStates == {"noncritical", "trying", "critical", "releasing"}

(***************************************************************************)
(* Type Invariant: lock and process states are always valid                *)
(***************************************************************************)

TypeInvariant ==
    /\ lock \in LockStates
    /\ pc \in [Procs -> PCStates]

(***************************************************************************)
(* Initial State: lock is unlocked, all processes in non-critical section  *)
(***************************************************************************)

Init ==
    /\ lock = "unlocked"
    /\ pc = [p \in Procs |-> "noncritical"]

(***************************************************************************)
(* Actions for each process                                                *)
(***************************************************************************)

(* Process p moves from non-critical section to trying to acquire lock *)
StartTrying(p) ==
    /\ pc[p] = "noncritical"
    /\ pc' = [pc EXCEPT ![p] = "trying"]
    /\ UNCHANGED lock

(* Process p acquires the lock (only possible when lock is unlocked) *)
AcquireLock(p) ==
    /\ pc[p] = "trying"
    /\ lock = "unlocked"
    /\ lock' = "locked"
    /\ pc' = [pc EXCEPT ![p] = "critical"]

(* Process p finishes critical section and begins releasing *)
StartReleasing(p) ==
    /\ pc[p] = "critical"
    /\ pc' = [pc EXCEPT ![p] = "releasing"]
    /\ UNCHANGED lock

(* Process p releases the lock and returns to non-critical section *)
ReleaseLock(p) ==
    /\ pc[p] = "releasing"
    /\ lock' = "unlocked"
    /\ pc' = [pc EXCEPT ![p] = "noncritical"]

(* All possible actions for process p *)
ProcessAction(p) ==
    \/ StartTrying(p)
    \/ AcquireLock(p)
    \/ StartReleasing(p)
    \/ ReleaseLock(p)

(***************************************************************************)
(* Next State Relation: interleaving of process actions                    *)
(***************************************************************************)

Next == \E p \in Procs : ProcessAction(p)

(***************************************************************************)
(* Fairness: Weak fairness for each process action                         *)
(* This ensures progress without violating safety                          *)
(***************************************************************************)

Fairness == \A p \in Procs : WF_vars(ProcessAction(p))

(***************************************************************************)
(* Complete Specification                                                  *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety Properties                                                       *)
(***************************************************************************)

(* Mutual Exclusion: at most one process in critical or releasing state *)
MutualExclusion ==
    \A p, q \in Procs :
        (p # q) => ~(pc[p] \in {"critical", "releasing"} /\ 
                     pc[q] \in {"critical", "releasing"})

(* Alternative formulation: cardinality of processes holding lock <= 1 *)
MutualExclusionAlt ==
    Cardinality({p \in Procs : pc[p] \in {"critical", "releasing"}}) <= 1

(* Lock Consistency: lock state matches whether any process holds it *)
LockConsistency ==
    /\ ((\E p \in Procs : pc[p] \in {"critical", "releasing"}) => lock = "locked")
    /\ ((\A p \in Procs : pc[p] \notin {"critical", "releasing"}) => lock = "unlocked")

(* Combined safety invariant *)
SafetyInvariant ==
    /\ TypeInvariant
    /\ MutualExclusion
    /\ LockConsistency

(***************************************************************************)
(* Liveness Properties (optional, enabled by fairness)                     *)
(***************************************************************************)

(* Every trying process eventually enters critical section *)
EventualEntry == \A p \in Procs : (pc[p] = "trying") ~> (pc[p] = "critical")

(* Every process in critical section eventually releases *)
EventualRelease == \A p \in Procs : (pc[p] = "critical") ~> (pc[p] = "noncritical")

(***************************************************************************)
(* Inductive Invariant Schema for Verification                             *)
(* This can be used to prove safety properties are preserved               *)
(***************************************************************************)

(* The inductive invariant combines type safety with mutual exclusion *)
InductiveInvariant ==
    /\ TypeInvariant
    /\ MutualExclusion
    /\ LockConsistency

(* Proof obligations (to be verified by TLC or TLAPS):                     *)
(* 1. Init => InductiveInvariant                                           *)
(* 2. InductiveInvariant /\ Next => InductiveInvariant'                    *)
(* 3. InductiveInvariant => SafetyInvariant                                *)

(***************************************************************************)
(* Theorems stating the properties to verify                               *)
(***************************************************************************)

THEOREM InitEstablishesInvariant == Init => InductiveInvariant

THEOREM InvariantPreserved == InductiveInvariant /\ Next => InductiveInvariant'

THEOREM SafetyHolds == Spec => []SafetyInvariant

=============================================================================