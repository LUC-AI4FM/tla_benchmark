------------------------------ MODULE TwoVarIncrement ------------------------------
(***************************************************************************)
(* A two-variable state machine.  Both components start at 1.  Each step   *)
(* either performs the increment transition on the first component, which *)
(* sets x to 2 and either leaves y unchanged or sets y to 1, or it         *)
(* stutters and leaves both components unchanged.                          *)
(***************************************************************************)
EXTENDS Naturals, Integers, TLC

VARIABLES x, y

vars == << x, y >>

TypeOK == x \in Int /\ y \in Int

-----------------------------------------------------------------------------
(* Initial state *)
Init ==
    /\ x = 1
    /\ y = 1

(* Increment variant 1: x becomes 2 and y is set to 1 *)
IncrementSetY ==
    /\ x' = 2
    /\ y' = 1

(* Increment variant 2: x becomes 2 and y is left unchanged *)
IncrementKeepY ==
    /\ x' = 2
    /\ UNCHANGED y

(* The increment transition for the first component *)
Increment ==
    \/ IncrementSetY
    \/ IncrementKeepY

(* Explicit "do nothing" step *)
Skip == UNCHANGED vars

Next ==
    \/ Increment
    \/ Skip

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety: x is always a natural number and at least 1.  The Assert calls  *)
(* report a diagnostic message if TLC finds a violation.                   *)
Inv ==
    /\ Assert(x \in Nat, <<"Violation: x is not a natural number", x>>)
    /\ Assert(x >= 1, <<"Violation: x < 1", x>>)
    /\ x \in Nat
    /\ x >= 1

(* Plain form of the safety invariant, without TLC side effects *)
SafetyInv == x \in Nat /\ x >= 1

(* Deterministic effect: any step that changes x sets it to 2 *)
DeterministicX == [][x' # x => x' = 2]_vars

(* Conditional consistency: when x becomes 2, y stays unchanged or becomes 1 *)
ConditionalY == [][(x' = 2 /\ x # 2) => (y' = y \/ y' = 1)]_vars

(* Combined action property *)
StepProperties ==
    [][ /\ (x' # x => x' = 2)
        /\ (x' = 2 => (y' = y \/ y' = 1)) ]_vars

(* Reachability: the state x = 2 /\ y = 1 is reachable.  To check it,     *)
(* use this as an invariant and expect TLC to report a violation, which   *)
(* is the witness trace.                                                  *)
TargetState == x = 2 /\ y = 1
NotTargetReachable == ~TargetState

(* Nontriviality: a state different from the initial state is reachable.  *)
(* To check it, use this as an invariant and expect TLC to report a       *)
(* violation.                                                             *)
NeverLeavesInit == x = 1 /\ y = 1

(* Diagnostic variant of Next that prints a message when x is incremented *)
NextWithLogging ==
    \/ /\ Increment
       /\ PrintT(<<"Increment step", "x'", x', "y'", y'>>)
    \/ Skip

=============================================================================