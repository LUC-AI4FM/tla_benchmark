---------------------------- MODULE PrimedCounter ----------------------------
(***************************************************************************)
(* A two-variable transition system: x is a counter, y an auxiliary value. *)
(* Init: x = 1, y = 3. Each step either increments x by one, leaving y     *)
(* unchanged, or stutters.                                                 *)
(*                                                                         *)
(* The increment is written in several equivalent ways. They are combined *)
(* by nondeterministic choice so that TLC exercises each of these forms:   *)
(*   - plain unprimed expressions of the pre-state,                        *)
(*   - expressions of the primed (post-state) variables,                   *)
(*   - the prime operator applied to a compound subexpression,             *)
(*   - LET-local definitions evaluated in the pre-state and, primed, in    *)
(*     the post-state.                                                     *)
(*                                                                         *)
(* MaxCount bounds the counter so that the state space is finite. TLC      *)
(* prints an error trace (counterexample) for any invariant, action        *)
(* property or temporal property that is violated.                         *)
(***************************************************************************)
EXTENDS Integers

CONSTANT MaxCount

ASSUME MaxCountOK == MaxCount \in Nat /\ MaxCount >= 1

VARIABLES x, y

vars == <<x, y>>

CounterRange == 0 .. MaxCount + 1

-----------------------------------------------------------------------------
(* Helper predicates and expressions on states *)

Even(v)  == v % 2 = 0
IsOne    == x = 1                (* evaluated in the pre-state            *)
Sum      == x + y                (* state function; Sum' is post-state    *)

-----------------------------------------------------------------------------
Init == /\ x = 1
        /\ y = 3

(* 1. Direct form: the primed variable equals an unprimed expression. *)
IncDirect ==
    /\ x < MaxCount
    /\ x' = x + 1
    /\ y' = y

(* 2. Relational form: a constraint on the difference of new and old x. *)
IncDifference ==
    /\ x < MaxCount
    /\ x' \in CounterRange
    /\ x' - x = 1
    /\ y' = y

(* 3. Prime applied to a compound subexpression: (x + y)' = x' + y'. *)
IncPrimedSubexpr ==
    /\ x < MaxCount
    /\ y' = y
    /\ x' \in CounterRange
    /\ (x + y)' = (x + y) + 1

(* 4. LET definition evaluated in the pre-state. *)
IncLetPre ==
    /\ x < MaxCount
    /\ LET nxt == x + 1          (* refers to the pre-state value of x *)
       IN  x' = nxt
    /\ y' = y

(* 5. LET definition that is primed, so it is evaluated in the post-state. *)
IncLetPost ==
    /\ x < MaxCount
    /\ y' = y
    /\ x' \in CounterRange
    /\ LET s == x + y
       IN  s' = s + 1           (* s' is post-state, s is pre-state *)

(* 6. Prime applied to a state predicate defined elsewhere. *)
IncPrimedOp ==
    /\ x < MaxCount
    /\ y' = y
    /\ x' \in CounterRange
    /\ Sum' = Sum + 1

Increment ==
    \/ IncDirect
    \/ IncDifference
    \/ IncPrimedSubexpr
    \/ IncLetPre
    \/ IncLetPost
    \/ IncPrimedOp

Stutter == UNCHANGED vars

Next == Increment \/ Stutter

Spec == Init /\ [][Next]_vars

(* Optional fair variant, used only for the liveness check below. *)
FairSpec == Spec /\ WF_vars(Increment)

-----------------------------------------------------------------------------
(***************************************************************************)
(* State invariants                                                        *)
(***************************************************************************)

TypeOK == /\ x \in CounterRange
          /\ y \in Int

(* The auxiliary value is always 3, including across stuttering steps. *)
AuxInvariant == y = 3

CounterBounds == 1 <= x /\ x <= MaxCount

(***************************************************************************)
(* Action properties, checked as temporal formulas [][A]_vars              *)
(***************************************************************************)

(* All transitions preserve the auxiliary value. *)
AuxPreserved == [][y' = y]_vars

(* Each increment variant, when taken, yields x' = x + 1. *)
IncrementCorrect ==
    [][ /\ IncDirect        => x' = x + 1
        /\ IncDifference    => x' = x + 1
        /\ IncPrimedSubexpr => x' = x + 1
        /\ IncLetPre        => x' = x + 1
        /\ IncLetPost       => x' = x + 1
        /\ IncPrimedOp      => x' = x + 1 ]_vars

(* Any step that changes the state is exactly an increment. *)
OnlyIncrements == [][x' = x + 1 /\ y' = y]_vars

(* Combined assertions over pre- and post-state values. A real increment   *)
(* moves x strictly up and flips its parity. Priming a predicate is the    *)
(* same as evaluating it on the primed variables.                          *)
PrePostAssertions ==
    [][ /\ x' > x
        /\ ~(x > x')
        /\ Even(x) # Even(x')
        /\ (x + 1)' = x' + 1
        /\ (x + y)' = x' + y'
        /\ Sum' = x' + y'
        /\ (IsOne' <=> (x' = 1))
        /\ (IsOne  <=> (x  = 1)) ]_vars

(* Primed references are evaluated against the post-state and unprimed     *)
(* references against the pre-state. If they were confused, x' - x would   *)
(* be 0 or -1, and Sum' - Sum would not be 1.                              *)
NoPrePostConfusion ==
    [][ /\ x' - x = 1
        /\ Sum' - Sum = 1
        /\ (LET d == x IN d' - d) = 1
        /\ (LET a == y IN a' = a) ]_vars

(* Stuttering is allowed and preserves everything, including y = 3. *)
StutterSafe == [][UNCHANGED vars => (y' = 3 /\ x' = x)]_vars

(***************************************************************************)
(* Liveness. This holds only under FairSpec: the counter eventually        *)
(* reaches MaxCount.                                                       *)
(***************************************************************************)
EventuallyMax == <>(x = MaxCount)

-----------------------------------------------------------------------------
(* Theorems to be checked with TLC *)
THEOREM Spec => [](TypeOK /\ AuxInvariant /\ CounterBounds)
THEOREM Spec => AuxPreserved /\ IncrementCorrect /\ OnlyIncrements
THEOREM Spec => PrePostAssertions /\ NoPrePostConfusion /\ StutterSafe
THEOREM FairSpec => EventuallyMax
=============================================================================