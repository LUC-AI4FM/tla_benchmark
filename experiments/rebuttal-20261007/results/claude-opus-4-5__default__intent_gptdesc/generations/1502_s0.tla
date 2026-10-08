---------------------------- MODULE AbstractTransitionSystem ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    InitialState,       \* The initial value of the state (an integer)
    Op,                 \* A function from states to sets of possible successor states
    InvariantSet,       \* The set of allowed states (safety invariant)
    TargetPredicate     \* A predicate (set) for reachability checking

VARIABLES
    state,              \* The current state value (an integer)
    reached             \* Boolean tracking if TargetPredicate has been satisfied

vars == <<state, reached>>

\* Type correctness invariant
TypeOK ==
    /\ state \in Int
    /\ reached \in BOOLEAN

\* Initial state predicate
Init ==
    /\ state = InitialState
    /\ reached = (InitialState \in TargetPredicate)

\* Enabled check: can we make a transition from current state?
Enabled ==
    Op[state] # {}

\* Next state relation: nondeterministically choose a successor from Op(state)
Step ==
    /\ Enabled
    /\ \E s \in Op[state]:
        /\ state' = s
        /\ reached' = (reached \/ (s \in TargetPredicate))

\* Stuttering step when no transition is possible (for completeness)
Stutter ==
    /\ ~Enabled
    /\ UNCHANGED vars

\* Combined next-state relation
Next ==
    Step \/ Stutter

\* Specification with weak fairness on Step (ensures progress when enabled)
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Step)

\* Strong fairness version for stronger liveness guarantees
SpecStrong ==
    Init /\ [][Next]_vars /\ SF_vars(Step)

--------------------------------------------------------------------------------
\* SAFETY PROPERTIES
--------------------------------------------------------------------------------

\* The state always remains within the invariant set
SafetyInvariant ==
    state \in InvariantSet

\* Combined safety: type correctness and invariant membership
Safety ==
    TypeOK /\ SafetyInvariant

\* The state is always in the domain of Op (Op is defined for current state)
OpDefined ==
    state \in DOMAIN Op

--------------------------------------------------------------------------------
\* DEADLOCK PROPERTIES
--------------------------------------------------------------------------------

\* No deadlock: Op(state) is always nonempty for reachable states
NoDeadlock ==
    Enabled

\* Deadlock state predicate (useful for model checking)
IsDeadlocked ==
    ~Enabled

\* Property: if we're not deadlocked, we can eventually make progress
CanProgress ==
    Enabled => <>(\E s \in Op[state]: state' = s)

--------------------------------------------------------------------------------
\* LIVENESS PROPERTIES
--------------------------------------------------------------------------------

\* If Op(state) is nonempty, eventually a transition occurs
LivenessProgress ==
    Enabled ~> (state' # state \/ ~Enabled')

\* The system always eventually either makes a transition or reaches deadlock
EventualProgress ==
    [](Enabled => <>~Enabled \/ <>(state # state))

\* Alternative: whenever enabled, eventually the state changes or becomes disabled
ProgressWhenEnabled ==
    []((Enabled /\ Op[state] # {}) => <>(state # state \/ Op[state] = {}))

--------------------------------------------------------------------------------
\* REACHABILITY PROPERTIES
--------------------------------------------------------------------------------

\* Eventually reach a state satisfying TargetPredicate
EventuallyReachTarget ==
    <>reached

\* State satisfying target predicate is reachable
ReachabilityProperty ==
    <>(state \in TargetPredicate)

\* Once reached, the reached flag stays true
ReachedPersistence ==
    [](reached => []reached)

\* If target is reachable via Op, it is eventually reached
\* (This is an assumption about Op that can be checked)
TargetReachable ==
    <>(state \in TargetPredicate)

--------------------------------------------------------------------------------
\* HELPER PREDICATES FOR MODEL CHECKING
--------------------------------------------------------------------------------

\* Check if current state can reach target in one step
CanReachTargetInOneStep ==
    \E s \in Op[state]: s \in TargetPredicate

\* Successor states of current state
Successors ==
    IF state \in DOMAIN Op THEN Op[state] ELSE {}

\* Check if all successors are in invariant set
SuccessorsInInvariant ==
    Enabled => (\A s \in Op[state]: s \in InvariantSet)

\* Inductive invariant candidate: if state is in invariant, successors are too
InductiveInvariant ==
    (state \in InvariantSet) => (\A s \in Successors: s \in InvariantSet)

================================================================================