---------------------------- MODULE BoundedCounter ----------------------------
(***************************************************************************)
(* A single integer-valued counter that can be incremented (up to Bound),  *)
(* reset to zero, and tested against a designated Target value.  The test *)
(* produces a boolean result that reflects counter = Target and does not  *)
(* modify the counter.  Operations may occur in any order and may repeat.  *)
(* Stuttering steps are permitted.                                         *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Bound,      \* fixed upper bound on the counter
    Target      \* designated target value tested by the Test operation

ASSUME BoundAssumption  == Bound \in Nat
ASSUME TargetAssumption == Target \in 0..Bound

VARIABLES
    counter,    \* the counter value
    result,     \* boolean outcome of the most recent Test
    lastOp      \* the most recent external operation performed

vars == <<counter, result, lastOp>>

Ops == {"none", "inc", "reset", "test"}

-----------------------------------------------------------------------------
(* Type correctness *)

TypeOK ==
    /\ counter \in Nat
    /\ counter \in 0..Bound
    /\ result \in BOOLEAN
    /\ lastOp \in Ops

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ counter = 0
    /\ result = (0 = Target)
    /\ lastOp = "none"

-----------------------------------------------------------------------------
(* Operations *)

\* (1) Increment: increase the counter by 1, but only if strictly below Bound.
\*     The stored test result is unaffected by an increment.
Increment ==
    /\ counter < Bound
    /\ counter' = counter + 1
    /\ result' = result
    /\ lastOp' = "inc"

\* (2) Reset: set the counter back to zero.
Reset ==
    /\ counter' = 0
    /\ result' = result
    /\ lastOp' = "reset"

\* (3) Test: check whether the counter equals Target and record the boolean
\*     result without modifying the counter.
Test ==
    /\ result' = (counter = Target)
    /\ counter' = counter
    /\ lastOp' = "test"

\* Operations may occur in any order and may repeat.
Next ==
    \/ Increment
    \/ Reset
    \/ Test

-----------------------------------------------------------------------------
(* Specification *)

\* The [Next]_vars form allows stuttering steps that leave the state unchanged.
\* Weak fairness on Increment ensures progress toward the target
\* when increments stay enabled.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Increment)

-----------------------------------------------------------------------------
(* Safety properties *)

\* The counter is always a natural number and never exceeds Bound.
CounterInRange ==
    /\ counter \in Nat
    /\ counter <= Bound

\* State-level form: right after a Test, the result is TRUE exactly when
\* the counter equals the target.
TestResultCorrect ==
    lastOp = "test" => (result = (counter = Target))

\* Action-level form: every Test step yields result' = (counter = Target).
\* The counter is unchanged by Test, so this equals the observed value at
\* that step.
TestStepCorrect ==
    [][Test => /\ result' = (counter = Target)
               /\ result' = (counter' = Target)]_vars

\* An Increment never changes the test result.  A test result can only
\* reflect the post-increment value through a subsequent Test step that
\* observes the new counter value.
IncrementPreservesResult ==
    [][Increment => result' = result]_vars

\* No operation other than Test may alter the result.
OnlyTestChangesResult ==
    [][(result' # result) => Test]_vars

\* Test never modifies the counter.
TestDoesNotModifyCounter ==
    [][Test => counter' = counter]_vars

\* Deadlock freedom: some operation is always enabled.
\* Reset is always enabled, and so is Test.
DeadlockFree ==
    ENABLED (Increment \/ Reset \/ Test)

\* Combined state invariant.
Inv ==
    /\ TypeOK
    /\ CounterInRange
    /\ TestResultCorrect
    /\ DeadlockFree

-----------------------------------------------------------------------------
(* Liveness properties *)

\* If no Reset ever intervenes, then from any state where the counter is
\* below the bound and not past the target, a sequence of increments
\* eventually brings the counter to the target value.
ReachTarget ==
    [][~Reset]_vars =>
        ((counter < Bound /\ counter <= Target) ~> (counter = Target))

\* Weaker form: if resets eventually stop forever, then whenever the counter
\* is below the target it eventually reaches it.
ReachTargetUnlessResetsRecur ==
    (<>[][~Reset]_vars) =>
        ((counter <= Target) ~> (counter = Target))

\* The system never gets stuck: some operation remains enabled forever.
NoDeadlock ==
    []ENABLED (Increment \/ Reset \/ Test)

\* If increments are uninterrupted by resets, the counter eventually
\* reaches the bound.
EventuallyBoundWithoutReset ==
    [][~Reset]_vars => <>(counter = Bound)

-----------------------------------------------------------------------------
(* Theorems *)

THEOREM Spec => []Inv
THEOREM Spec => TestStepCorrect
THEOREM Spec => IncrementPreservesResult
THEOREM Spec => OnlyTestChangesResult
THEOREM Spec => TestDoesNotModifyCounter
THEOREM Spec => NoDeadlock
THEOREM Spec => ReachTarget
THEOREM Spec => ReachTargetUnlessResetsRecur

=============================================================================