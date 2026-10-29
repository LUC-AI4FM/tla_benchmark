------------------------------ MODULE TwoVarStateMachine ------------------------------
(***************************************************************************)
(* A two-variable state machine that evolves in discrete steps.            *)
(*  - x, y are integer-valued and both start at 1.                         *)
(*  - In each step the system either performs the increment transition     *)
(*    (x' = 2, and y' is either set to 1 or left unchanged) or stutters.   *)
(*  - TLC's Print/Assert operators support diagnostics during checking.    *)
(***************************************************************************)
EXTENDS Naturals, Integers, TLC

CONSTANT Debug          \* BOOLEAN: when TRUE, diagnostic messages are printed

ASSUME DebugIsBoolean == Debug \in BOOLEAN

VARIABLES x, y

vars == <<x, y>>

---------------------------------------------------------------------------------------
(* Diagnostics helpers *)

Log(msg, val) == IF Debug THEN PrintT(<<msg, val>>) ELSE TRUE

Check(cond, msg) == Assert(cond, msg)

---------------------------------------------------------------------------------------
(* Type information *)

TypeOK == /\ x \in Int
          /\ y \in Int

---------------------------------------------------------------------------------------
(* Initial state *)

Init == /\ x = 1
        /\ y = 1
        /\ Log("Init", <<1, 1>>)

---------------------------------------------------------------------------------------
(* Increment transition: x is set deterministically to 2; y is either set  *)
(* to 1 or left unchanged.                                                 *)

IncrSetY ==
    /\ x' = 2
    /\ y' = 1
    /\ Check(x' = 2, "Deterministic effect violated in IncrSetY: x' # 2")
    /\ Log("IncrSetY", <<x, y, x', y'>>)

IncrKeepY ==
    /\ x' = 2
    /\ y' = y
    /\ Check(x' = 2, "Deterministic effect violated in IncrKeepY: x' # 2")
    /\ Log("IncrKeepY", <<x, y, x', y'>>)

Incr == IncrSetY \/ IncrKeepY

(* Explicit "do nothing" step *)
Skip == /\ UNCHANGED vars
        /\ Log("Skip", <<x, y>>)

Next == Incr \/ Skip

(* Weak fairness on the increment ensures progress for the liveness checks. *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Incr)

---------------------------------------------------------------------------------------
(* Safety invariants *)

XIsNat == x \in Nat

XAtLeastOne == x >= 1

SafetyInv == /\ TypeOK
             /\ XIsNat
             /\ XAtLeastOne

(* Reachability witness: TLC reporting a violation of this invariant       *)
(* demonstrates that the state x = 2 /\ y = 1 is reachable.                *)
TargetNotReached == ~(x = 2 /\ y = 1)

(* Nontriviality witness: TLC reporting a violation of this invariant      *)
(* demonstrates that a reachable state distinct from the initial one exists.*)
StuckInInit == x = 1 /\ y = 1

---------------------------------------------------------------------------------------
(* Action (step) properties *)

(* Whenever the transition changes x, the new value of x is exactly 2. *)
DeterministicX == [][(x' # x) => (x' = 2)]_vars

(* Whenever x becomes 2 in a step, y is either unchanged or set to 1. *)
ConditionalConsistency == [][(x' = 2) => (y' = y \/ y' = 1)]_vars

(* Every step that changes x is an Incr step. *)
OnlyIncrChangesX == [][(x' # x) => Incr]_vars

---------------------------------------------------------------------------------------
(* Liveness properties *)

(* Reachability: from the initial state, x = 2 /\ y = 1 is eventually reached. *)
ReachTarget == <>(x = 2 /\ y = 1)

(* Nontriviality: the system eventually leaves the initial state. *)
Nontrivial == <>(x # 1 \/ y # 1)

(* Once x = 2, it stays 2. *)
StableAtTwo == [](x = 2 => [](x = 2))

---------------------------------------------------------------------------------------
(* Theorems *)

THEOREM Spec => []SafetyInv
THEOREM Spec => DeterministicX
THEOREM Spec => ConditionalConsistency
THEOREM Spec => ReachTarget
THEOREM Spec => Nontrivial

=======================================================================================