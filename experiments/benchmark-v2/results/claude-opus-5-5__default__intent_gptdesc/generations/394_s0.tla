---------------------------- MODULE BranchStepSystem ----------------------------
EXTENDS Integers, TLC

CONSTANTS
    InitX,      \* fixed initial value of the first component
    InitY,      \* fixed initial value of the second component
    Target,     \* value of x that selects the "success" branch
    Limit       \* bound on increments (keeps the state space finite)

ASSUME /\ InitX \in Int
       /\ InitY \in Int
       /\ Target \in Int
       /\ Limit \in Int
       /\ InitX <= Limit
       /\ InitY <= Limit

VARIABLES
    x,          \* first integer state component
    y,          \* second integer state component
    branch      \* record of the most recent branch outcome

vars == << x, y, branch >>

Branches == {"init", "incX", "incY", "success", "other"}

-----------------------------------------------------------------------------
(* Initial state: fixed values *)

Init ==
    /\ x = InitX
    /\ y = InitY
    /\ branch = "init"

-----------------------------------------------------------------------------
(* Actions *)

\* Increment x and leave y unchanged
IncX ==
    /\ x < Limit
    /\ x' = x + 1
    /\ y' = y
    /\ branch' = "incX"

\* Increment y and leave x unchanged
IncY ==
    /\ y < Limit
    /\ y' = y + 1
    /\ x' = x
    /\ branch' = "incY"

\* Conditional step. When x equals Target, it increments x and records "success".
\* Otherwise it increments x and records "other". Embedded assertions check that
\* the postcondition of the chosen branch holds. They use primed and unprimed values.
CondStep ==
    /\ x < Limit
    /\ IF x = Target
         THEN /\ x' = x + 1
              /\ branch' = "success"
              /\ Assert(x' = Target + 1, "success branch postcondition failed")
         ELSE /\ x' = x + 1
              /\ branch' = "other"
              /\ Assert(x' # Target + 1, "other branch postcondition failed")
    /\ y' = y

\* Explicit stuttering step: both components remain unchanged
Stutter ==
    UNCHANGED vars

Update == IncX \/ IncY \/ CondStep

Next ==
    \/ Update
    \/ Stutter

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(CondStep)
    /\ WF_vars(IncX)

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ x \in Int
    /\ y \in Int
    /\ branch \in Branches

Bounds ==
    /\ InitX <= x /\ x <= Limit
    /\ InitY <= y /\ y <= Limit

\* The recorded branch matches the state that results from it
BranchConsistent ==
    /\ branch = "success" => x = Target + 1
    /\ branch = "other"   => x # Target + 1
    /\ branch = "init"    => (x = InitX /\ y = InitY)

\* A trivially true invariant. It acts as a sanity check that the embedded
\* assertions never fail. If one did fail, TLC would report an assertion error.
AssertionsNeverFail == TRUE

\* A trivially true invariant about whether predicates can be evaluated
TriviallyTrue == x = x /\ y = y

-----------------------------------------------------------------------------
(* Action / transition properties: primed vs. unprimed semantics *)

\* Only allowed transitions occur
AllowedTransitions == [][Next]_vars

\* Each step either increments exactly one component by 1 or changes nothing
StepShape ==
    [][ \/ (x' = x + 1 /\ y' = y)
        \/ (y' = y + 1 /\ x' = x)
        \/ (x' = x /\ y' = y) ]_vars

\* Deterministic update semantics for each chosen branch:
\* if the precondition holds and the branch is taken, the postcondition holds
SuccessBranchSemantics ==
    [][ (CondStep /\ x = Target) => (x' = x + 1 /\ y' = y /\ branch' = "success") ]_vars

OtherBranchSemantics ==
    [][ (CondStep /\ x # Target) => (x' = x + 1 /\ y' = y /\ branch' = "other") ]_vars

\* A step that records "success" must have started from x = Target.
\* This compares the unprimed precondition with the primed postcondition.
SuccessRequiresPrecondition ==
    [][ (branch' = "success" /\ branch' # branch \/ (branch' = "success" /\ x' # x))
          => x = Target ]_vars

\* The components never decrease
Monotonic ==
    [][ x' >= x /\ y' >= y ]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Whenever the increment branch is enabled, a real (non-stuttering)
\* update eventually happens
IncrementProgress ==
    []( ENABLED <<CondStep>>_vars => <><<Update>>_vars )

\* x eventually reaches its bound
EventuallyLimit ==
    (x < Limit) ~> (x = Limit)

=============================================================================