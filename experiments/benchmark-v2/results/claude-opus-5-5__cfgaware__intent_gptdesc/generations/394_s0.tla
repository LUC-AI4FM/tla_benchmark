---------------------------- MODULE CondIncrement ----------------------------
EXTENDS Integers, TLC

VARIABLES x, y, branch

vars == <<x, y, branch>>

\* Bound keeps the state space finite for model checking.
Bound == 4

Branches == {"none", "incX", "incY", "success", "other"}

TypeOK ==
    /\ x \in Int
    /\ y \in Int
    /\ x \in 0..Bound
    /\ y \in 0..Bound
    /\ branch \in Branches

Init ==
    /\ x = 0
    /\ y = 0
    /\ branch = "none"

\* Increment x, leave y unchanged.
IncX ==
    /\ x < Bound
    /\ x' = x + 1
    /\ y' = y
    /\ branch' = "incX"
    /\ Assert(x' = x + 1, "IncX postcondition failed")

\* Increment y, leave x unchanged.
IncY ==
    /\ y < Bound
    /\ y' = y + 1
    /\ x' = x
    /\ branch' = "incY"
    /\ Assert(y' = y + 1, "IncY postcondition failed")

\* Conditional step: branch outcome depends on the pre-state value of x.
CondStep ==
    /\ x < Bound
    /\ y' = y
    /\ IF x = 1
         THEN /\ x' = x + 1
              /\ branch' = "success"
              /\ Assert(x = 1 /\ x' = 2, "success branch postcondition failed")
         ELSE /\ x' = x + 1
              /\ branch' = "other"
              /\ Assert(x # 1 /\ x' # 2, "other branch postcondition failed")

\* Stuttering step: keep both components unchanged.
Stutter ==
    UNCHANGED vars

Next ==
    \/ IncX
    \/ IncY
    \/ CondStep
    \/ Stutter

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(IncX)
    /\ WF_vars(IncY)

-----------------------------------------------------------------------------
\* Invariants

BranchConsistent ==
    /\ branch = "success" => x = 2
    /\ branch = "other"   => x # 2 /\ x >= 1
    /\ branch = "incX"    => x >= 1
    /\ branch = "incY"    => y >= 1
    /\ branch = "none"    => x = 0 /\ y = 0

TriviallyTrue == TRUE

Inv ==
    /\ TypeOK
    /\ BranchConsistent
    /\ TriviallyTrue

-----------------------------------------------------------------------------
\* Action-level and temporal properties

\* Every step follows only allowed transitions with correct pre/post semantics.
StepSemantics ==
    [][ /\ (branch' = "success" /\ branch' # branch) => (x = 1 /\ x' = 2)
        /\ (x' # x) => (x' = x + 1 /\ y' = y)
        /\ (y' # y) => (y' = y + 1 /\ x' = x)
      ]_vars

\* Monotonicity: components never decrease.
Monotone == [][x' >= x /\ y' >= y]_vars

\* Liveness: whenever the increment branch is enabled, a non-stuttering
\* update of x eventually occurs.
Progress == \A v \in 0..(Bound - 1) :
    (x = v /\ ENABLED IncX) ~> (x > v)

THEOREM Spec => []Inv
=============================================================================