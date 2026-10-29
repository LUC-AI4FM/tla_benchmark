---------------------------- MODULE OpTransitionSystem ----------------------------
(***************************************************************************)
(* A simple state-transition system whose state is one integer variable    *)
(* x. Each step picks a successor from Op(x). Op is an abstract operation  *)
(* family: a map from states to sets of states, which may be               *)
(* nondeterministic, partial (empty set) or total. To check another        *)
(* instance, replace the definitions of Op, InitValue, InvSet and Target,  *)
(* or override them in the model configuration.                            *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

VARIABLE x

vars == << x >>

-----------------------------------------------------------------------------
(* Parameters, given concrete default definitions.                          *)
-----------------------------------------------------------------------------

\* Initial state value.
InitValue == 0

\* The bound used by the default instance.
Bound == 42

\* The abstract operation family: state -> set of possible next states.
\* Default instance: nondeterministically stay or step up by one or two,
\* without going past Bound, and wrap back to 0 once Bound is reached.
\* Op(s) is nonempty for every reachable s, so there is no deadlock.
Op(s) ==
    IF s < Bound
        THEN { t \in {s, s + 1, s + 2} : t <= Bound }
        ELSE {0}

\* User-specified invariant set.
InvSet == 0..Bound

\* Predicate used for reachability.
Target(s) == s = Bound

-----------------------------------------------------------------------------
(* Specification                                                            *)
-----------------------------------------------------------------------------

Init == x = InitValue

\* Every transition picks the next state from Op(current).
Next == \E t \in Op(x) : x' = t

\* Weak fairness: if Op(x) stays nonempty, the system eventually moves.
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties                                                               *)
-----------------------------------------------------------------------------

TypeOK == x \in Int

\* Safety: the state always remains inside the invariant set.
\* For the default instance, this means x stays within 0..42.
Forty2 == x \in InvSet

InvariantHolds == [](x \in InvSet)

\* No deadlock: Op maps every reachable state to a nonempty set.
NoDeadlock == Op(x) # {}

\* Liveness: whenever Op(x) is nonempty, a transition is enabled and
\* (under fairness) a step is eventually taken.
CanAlwaysStep == [](Op(x) # {} => ENABLED Next)

Progress == [](Op(x) # {} => <>(\E t \in Op(x) : TRUE))

\* Reachability: some state satisfying Target is eventually reached.
\* Under weak fairness alone this need not hold, because stuttering
\* choices such as x' = x are allowed. It is provided for instances
\* where Op guarantees progress.
ReachTarget == <>(Target(x))

\* Invariant to check that a Target state can be reached: TLC reports a
\* counterexample trace leading to a Target state if one exists.
TargetNotReached == ~Target(x)

=============================================================================