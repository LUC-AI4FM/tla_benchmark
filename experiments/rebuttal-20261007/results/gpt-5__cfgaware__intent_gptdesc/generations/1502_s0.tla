---- MODULE OpSystem ----
EXTENDS Naturals, Integers

CONSTANTS
  Op,         \* A (possibly partial, nondeterministic) function from Int to SUBSET Int
  InitVal,    \* Initial integer state value
  InvSet,     \* Allowed invariant set of states (subset of Int)
  TargetSet   \* Target set for reachability checks

VARIABLES s    \* Single integer-valued state variable

\* Type and shape assumptions for constants (checked/used by TLC when possible)
ASSUME
  /\ InitVal \in Int
  /\ InvSet \subseteq Int
  /\ TargetSet \subseteq Int
  /\ \A x \in DOMAIN Op: x \in Int /\ Op[x] \subseteq Int

\* Helper: the set of permitted successors from u, constrained by the invariant set.
NextStates(u) == IF u \in DOMAIN Op THEN (Op[u] \cap InvSet) ELSE {}

\* Initial condition
Init ==
  /\ s = InitVal
  /\ s \in InvSet
  /\ s \in Int

\* Transition relation: every step picks the next state from Op(s), restricted to InvSet.
Next ==
  s' \in NextStates(s)

\* Standard temporal specification with weak fairness to express progress when enabled.
Spec ==
  Init /\ [][Next]_s /\ WF_s(Next)

\* Safety: state always remains in the invariant set; and stays an integer.
Safety == [](s \in InvSet)
TypeOK == [](s \in Int)

\* Liveness/enablement-related predicates and properties.
OpEnabled == /\ s \in DOMAIN Op /\ Op[s] # {}
DeadlockFree == [] (Enabled Next)
NoDeadlockWhenOpNonEmpty == [] (OpEnabled => Enabled Next)

\* Reachability: eventually reach some state in TargetSet.
Reachability == <> (s \in TargetSet)

\* Required constant/operator for configuration binding.
Forty2 == 42

====