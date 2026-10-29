------------------------------ MODULE ModCounter ------------------------------
(***************************************************************************)
(* A discrete-time counter that increments modulo N at every step.        *)
(*                                                                         *)
(*   counter : the observable counter value, initially 0.                  *)
(*   age     : a ghost (history) variable.  age[v] is the number of steps  *)
(*             since value v was last held by the counter.  It is          *)
(*             initialised as if the system had already been running      *)
(*             periodically before time 0, so age[v] = (0 - v) mod N.      *)
(*             It does not affect the counter's behaviour.  It lets the    *)
(*             periodicity property ("v recurs at least every N steps")    *)
(*             be checked as a finite-state invariant.                     *)
(*                                                                         *)
(* To model check, instantiate N with a concrete value (e.g. N <- 5) and   *)
(* TargetK with some k in 0..N-1, as in the MC module at the end.          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,        \* modulus, a natural number > 0
    TargetK   \* a value k in 0..N-1 for the "eventually counter = k" check

ASSUME NAssumption == N \in Nat /\ N > 0
ASSUME TargetKAssumption == TargetK \in 0..(N - 1)

VARIABLES counter, age

vars == <<counter, age>>

Values == 0..(N - 1)

\* The deterministic successor function.
Succ(c) == (c + 1) % N

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ counter = 0
    /\ age = [v \in Values |-> (N - v) % N]

(* The single action: exactly one increment per step. *)
Increment ==
    /\ counter' = Succ(counter)
    /\ age' = [v \in Values |-> IF v = Succ(counter) THEN 0 ELSE age[v] + 1]

Next == Increment

(* Strong fairness on the cyclic increment, as required. *)
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)

-----------------------------------------------------------------------------
(* Safety *)

TypeOK ==
    /\ counter \in Values
    /\ age \in [Values -> Values]

\* The counter is always an integer in 0..N-1.
SafetyInv == counter \in Nat /\ 0 <= counter /\ counter <= N - 1

-----------------------------------------------------------------------------
(* Determinism *)

\* From any state, exactly one successor counter value satisfies Next.
DeterminismInv ==
    Cardinality({d \in Values : d = Succ(counter)}) = 1

\* The transition is always enabled (no deadlock).
AlwaysEnabledInv == ENABLED Next

\* Every step that changes the state is exactly the increment.
DeterministicStep == [][counter' = Succ(counter)]_vars

-----------------------------------------------------------------------------
(* Periodicity *)

\* age[v] counts the steps since v was last seen; it never reaches N,
\* so every value v recurs at least every N steps.
PeriodicityInv ==
    /\ \A v \in Values : age[v] < N
    /\ age[counter] = 0
    /\ \A v \in Values : age[v] = (counter + N - v) % N

\* Since counter = age[0] (steps since 0, mod N), after exactly N steps the
\* counter returns to its starting value.  Each step advances the value by
\* exactly one, mod N.
OneStepAdvance ==
    [][counter' = Succ(counter) /\ age'[counter] = 1 % N]_vars

-----------------------------------------------------------------------------
(* Liveness and temporal assertions *)

\* Eventually the counter equals k.
EventuallyEquals(k) == <>(counter = k)

EventuallyTarget == EventuallyEquals(TargetK)

EventuallyEveryValue == \A k \in Values : EventuallyEquals(k)

\* Every value in 0..N-1 is visited infinitely often.
InfinitelyOften == \A k \in Values : []<>(counter = k)

\* Each value is always followed by its successor.
ProgressLeadsTo == \A v \in Values : (counter = v) ~> (counter = Succ(v))

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []SafetyInv
THEOREM Spec => []DeterminismInv
THEOREM Spec => []PeriodicityInv
THEOREM Spec => DeterministicStep
THEOREM Spec => InfinitelyOften
THEOREM Spec => EventuallyTarget
THEOREM Spec => ProgressLeadsTo

(***************************************************************************)
(* Example TLC configuration (ModCounter.cfg):                             *)
(*                                                                         *)
(*   CONSTANTS N = 5  TargetK = 3                                          *)
(*   SPECIFICATION Spec                                                    *)
(*   INVARIANTS TypeOK SafetyInv DeterminismInv AlwaysEnabledInv           *)
(*              PeriodicityInv                                             *)
(*   PROPERTIES DeterministicStep OneStepAdvance EventuallyTarget          *)
(*              EventuallyEveryValue InfinitelyOften ProgressLeadsTo       *)
(***************************************************************************)
=============================================================================