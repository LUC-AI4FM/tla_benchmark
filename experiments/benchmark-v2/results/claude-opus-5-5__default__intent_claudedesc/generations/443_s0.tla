------------------------------ MODULE EnabledSubst ------------------------------
(***************************************************************************)
(* Semantic test of the ENABLED operator under parameter substitution.     *)
(*                                                                         *)
(* Foo(v, A) checks enabledness of a disjunction of three actions:         *)
(*   1. the action argument A,                                             *)
(*   2. a stuttering-like step on the parameter v   (v' = v),              *)
(*   3. a swap-like step between v and module variable y                   *)
(*      (v' = y /\ y' = v).                                                *)
(*                                                                         *)
(* Bar instantiates v with the module variable y itself, so y occurs both  *)
(* as a substituted formal parameter and as a free variable, and y' occurs *)
(* in several disjuncts inside the ENABLED context.                        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N > 1

VARIABLES x, y

vars == <<x, y>>

Vals == 0 .. (N - 1)

TypeOK == x \in Vals /\ y \in Vals

(* Parameterized operator: v is a variable parameter, A an action parameter *)
Foo(v, A) == ENABLED (A \/ v' = v \/ (v' = y /\ y' = v))

(* Composed action: y unchanged, conjoined with an invocation of Foo where *)
(* the formal parameter v is instantiated by the module variable y.        *)
Bar == y' = y /\ Foo(y, x' = 1)

(* Variant in which the parameter is instantiated by x instead of y, so   *)
(* the swap disjunct really exchanges two distinct variables.             *)
Baz == x' = x /\ Foo(x, y' = 1)

-----------------------------------------------------------------------------

Init == x = 0 /\ y = 0

IncX == Bar /\ x' = (x + 1) % N

IncY == Baz /\ y' = (y + 1) % N

Swap == x' = y /\ y' = x

Next == IncX \/ IncY \/ Swap

Spec == Init /\ [][Next]_vars /\ WF_vars(IncX) /\ WF_vars(IncY)

-----------------------------------------------------------------------------
(* Safety properties                                                       *)

(* The stuttering disjunct (v' = v) is always satisfiable, so the ENABLED *)
(* expression inside Foo must be TRUE in every state, regardless of how   *)
(* the formal parameter is bound.                                          *)
FooAlwaysEnabledY == Foo(y, x' = 1)
FooAlwaysEnabledX == Foo(x, y' = 1)
FooWithFalseAction == Foo(y, FALSE) /\ Foo(x, FALSE)

(* Since y' = y can always be satisfied together with the (always TRUE)   *)
(* state predicate Foo(y, x' = 1), Bar and Baz are always enabled.         *)
BarEnabled == ENABLED Bar
BazEnabled == ENABLED Baz

(* Enabledness of the composite matches the expected expansion when the   *)
(* substitution v <- y is performed correctly (no variable capture).       *)
SubstitutionCorrect ==
    Foo(y, x' = 1) = ENABLED ((x' = 1) \/ (y' = y) \/ (y' = y /\ y' = y))

(* The swap disjunct alone, with v <- x, is enabled in every state.        *)
SwapEnabled == ENABLED (x' = y /\ y' = x)

(* With v <- y, the swap disjunct is consistent only because y' = y twice. *)
SelfSwapEnabled == ENABLED (y' = y /\ y' = y)

(* A contradictory constraint must not be reported as enabled.             *)
ContradictionDisabled == ~ ENABLED (y' = y /\ y' # y)

Inv ==
    /\ TypeOK
    /\ FooAlwaysEnabledY
    /\ FooAlwaysEnabledX
    /\ FooWithFalseAction
    /\ BarEnabled
    /\ BazEnabled
    /\ SubstitutionCorrect
    /\ SwapEnabled
    /\ SelfSwapEnabled
    /\ ContradictionDisabled

-----------------------------------------------------------------------------
(* Liveness properties                                                     *)

XCycles == []<>(x = 0) /\ []<>(x = 1)
YCycles == []<>(y = 0) /\ []<>(y = 1)

Liveness == XCycles /\ YCycles

THEOREM Spec => []Inv
=============================================================================