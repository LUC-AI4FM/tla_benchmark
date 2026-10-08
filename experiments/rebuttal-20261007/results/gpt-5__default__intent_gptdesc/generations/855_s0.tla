----------------------------- MODULE PrisonersSwitches -----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
    N,         \* number of prisoners, with N > 1
    Counter    \* the designated counter, an element of 1..N

ASSUME N \in Nat \ {0, 1}
ASSUME Counter \in 1..N

(*
State and parameters
*)
Prisoners == 1..N
NonCounters == Prisoners \ {Counter}
Switches == {"sig", "aux"}  \* two independent binary switches: "sig" (signal), "aux" (auxiliary)

VARIABLES
    sw,            \* [Switches -> {0,1}] current switch positions
    visitedOnce,   \* [Prisoners -> BOOLEAN] ghost: has prisoner p been taken to the room at least once
    contributed,   \* [Prisoners -> BOOLEAN] for p != Counter: has p made their one-time contribution (set "sig" from 0 to 1)
    tally,         \* Nat, maintained by Counter: number of counted contributions
    declared       \* BOOLEAN, terminal signaling condition made by the counter

vars == << sw, visitedOnce, contributed, tally, declared >>

(*
Initialization:
- All switches start at 0.
- No one has visited, no one has contributed.
- Counter's tally is 0 and no declaration has been made.
*)
Init ==
    /\ sw \in [Switches -> {0,1}]
    /\ sw = [ s \in Switches |-> 0 ]
    /\ visitedOnce = [ p \in Prisoners |-> FALSE ]
    /\ contributed = [ p \in Prisoners |-> FALSE ]
    /\ tally = 0
    /\ declared = FALSE

(*
Helper definitions
*)
ContribSet == { p \in NonCounters : contributed[p] }
AllVisited == \A p \in Prisoners : visitedOnce[p]

(*
Type and basic discipline invariants (expressed as state predicates)
*)
TypeOK ==
    /\ sw \in [Switches -> {0,1}]
    /\ visitedOnce \in [Prisoners -> BOOLEAN]
    /\ contributed \in [Prisoners -> BOOLEAN]
    /\ contributed[Counter] = FALSE
    /\ tally \in 0..Cardinality(NonCounters)
    /\ declared \in BOOLEAN

(*
Key accounting invariant:
At all times, the counter’s tally plus the signal bit equals the number of
non-counter prisoners who have contributed so far.
This relies on the discipline that:
- A non-counter, at most once, raises "sig" from 0 to 1 to mark their first contribution.
- Only the counter lowers "sig" from 1 to 0 and increments tally by 1.
*)
AccountingInv ==
    tally + sw["sig"] = Cardinality(ContribSet)

(*
Safety: a declaration may be made only when everyone has visited at least once.
This is guaranteed by only allowing the counter to declare when tally = N-1,
and the accounting discipline ensures that implies every non-counter has visited at least once;
the counter trivially has visited if he can declare.
We also state this directly as a state predicate that should hold in all reachable states.
*)
SafeDecl ==
    declared => AllVisited

(*
Per-step actions: exactly one prisoner is chosen and performs exactly one
atomic switch operation (flip or set of a single switch), along with possible local bookkeeping.
Deterministic strategy:
- Non-counter prisoners:
  * On their first contribution opportunity (contributed[p] = FALSE and sw["sig"] = 0),
    set sw["sig"] := 1 and set contributed[p] := TRUE.
  * Otherwise, flip the auxiliary switch sw["aux"] to fulfill the "one atomic change" requirement.
- Counter:
  * If sw["sig"] = 1, set it to 0 and increment tally by 1.
  * Else if tally = N-1 and not declared, toggle sw["aux"] and set declared := TRUE.
  * Else, toggle sw["aux"].
All steps also mark visitedOnce[p] := TRUE for the chosen prisoner.
*)

NonCounterAct(p) ==
    /\ p \in NonCounters
    /\ visitedOnce' = [visitedOnce EXCEPT ![p] = TRUE]
    /\ IF ~contributed[p] /\ sw["sig"] = 0
          THEN /\ contributed' = [contributed EXCEPT ![p] = TRUE]
               /\ sw' = [sw EXCEPT !["sig"] = 1]
          ELSE /\ contributed' = contributed
               /\ sw' = [sw EXCEPT !["aux"] = 1 - sw["aux"]]
    /\ tally' = tally
    /\ declared' = declared

CounterAct ==
    /\ visitedOnce' = [visitedOnce EXCEPT ![Counter] = TRUE]
    /\ contributed' = contributed
    /\ IF sw["sig"] = 1
          THEN /\ sw' = [sw EXCEPT !["sig"] = 0]
               /\ tally' = tally + 1
               /\ declared' = declared
          ELSE IF ~declared /\ tally = Cardinality(NonCounters)
                  THEN /\ sw' = [sw EXCEPT !["aux"] = 1 - sw["aux"]]
                       /\ tally' = tally
                       /\ declared' = TRUE
                  ELSE /\ sw' = [sw EXCEPT !["aux"] = 1 - sw["aux"]]
                       /\ tally' = tally
                       /\ declared' = declared

Step(p) ==
    IF p = Counter
       THEN CounterAct
       ELSE NonCounterAct(p)

Next ==
    \E p \in Prisoners : Step(p)

(*
Temporal specification with strong fairness:
- At each step exactly one prisoner acts (Next).
- Every prisoner is chosen infinitely often (strong fairness of Step(p)), satisfying the
  "no starvation" assumption.
*)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in Prisoners : SF_vars(Step(p))

(*
Collect safety invariants used to justify correctness.
These are expected to hold in all reachable states of Spec.
*)
Inv ==
    /\ TypeOK
    /\ AccountingInv
    /\ SafeDecl

(*
Liveness requirement: Eventually, the protocol reaches the terminal signaling condition.
Under the strong fairness of each prisoner’s step (included in Spec), the counter will
eventually declare.
*)
Liveness ==
    <>declared

THEOREM SafetyInvariantHolds == Spec => []Inv
THEOREM EventualDeclaration == Spec => Liveness

=============================================================================