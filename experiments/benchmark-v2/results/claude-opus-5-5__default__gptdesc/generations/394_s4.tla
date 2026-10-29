---------------------------- MODULE PrimingSemantics ----------------------------
(***************************************************************************)
(* Regression-style test of the semantics of priming in TLA+.             *)
(* It exercises priming of:                                                *)
(*   - direct variable references,                                         *)
(*   - operator applications (with and without arguments),                 *)
(*   - LET-bound names (state-dependent and constant ones),                *)
(*   - conditional (IF/THEN/ELSE and CASE) expressions.                    *)
(* TLC's Print/PrintT and Assert are used to check expected behaviour.     *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANTS MaxVal

ASSUME MaxVal \in Nat /\ MaxVal > 0

VARIABLES x, y

vars == <<x, y>>

---------------------------------------------------------------------------
(* Helper operators                                                        *)
---------------------------------------------------------------------------

\* A zero-argument operator whose body depends on state variables.
Sum == x + y

\* An operator with a parameter; only the variable part is affected by priming.
Plus(a) == a + x

\* An operator that takes another state expression as an argument.
Twice(e) == e + e

\* A constant-level operator: priming it must not change its value.
Const == MaxVal

\* A conditional operator.
Pick == IF x = 0 THEN y ELSE x

\* The "next" value of x, as a function of the current state.
NextX == (x + 1) % (MaxVal + 1)

---------------------------------------------------------------------------

Init ==
    /\ x = 0
    /\ y = 0

TypeOK ==
    /\ x \in 0..MaxVal
    /\ y \in 0..MaxVal

Next ==
    /\ x' = NextX
    /\ y' = x
    \* 1. Direct variable priming
    /\ Assert(x' = (x + 1) % (MaxVal + 1), "Direct priming of x failed")
    /\ Assert(y' = x, "Direct priming of y failed")
    \* 2. Priming a zero-argument operator application
    /\ Assert(Sum' = x' + y', "Priming of operator Sum failed")
    \* 3. Priming an operator application with an argument
    /\ Assert(Plus(1)' = 1 + x', "Priming of Plus(1) failed")
    /\ Assert(Plus(y)' = y' + x', "Priming of Plus(y) failed")
    \* 4. Priming of an operator applied to a state expression
    /\ Assert(Twice(x)' = x' + x', "Priming of Twice(x) failed")
    /\ Assert(Twice(x') = 2 * x', "Twice applied to primed argument failed")
    \* 5. Priming of a constant-level operator
    /\ Assert(Const' = MaxVal, "Priming of constant operator changed value")
    \* 6. LET-bound names: state-dependent, constant, and action-level
    /\ LET z == x + y
           c == 5
           nx == x'
       IN  /\ Assert(z' = x' + y', "Priming of LET-bound state expression failed")
           /\ Assert(c' = 5, "Priming of LET-bound constant failed")
           /\ Assert(nx = NextX, "LET-bound primed variable failed")
           /\ Assert(z = Sum, "Unprimed LET-bound name differs from Sum")
    \* 7. Priming conditional expressions
    /\ Assert(Pick' = IF x' = 0 THEN y' ELSE x',
              "Priming of IF via operator failed")
    /\ Assert((IF x = 0 THEN y ELSE x)' = IF x' = 0 THEN y' ELSE x',
              "Priming of inline IF failed")
    /\ Assert((CASE x = 0 -> 10 [] OTHER -> x)' =
                (CASE x' = 0 -> 10 [] OTHER -> x'),
              "Priming of CASE failed")
    \* 8. Unprimed and primed must not be confused
    /\ Assert(Sum = x + y, "Unprimed Sum changed after assignment")
    /\ PrintT(<<"x", x, "y", y, "x'", x', "y'", y', "Sum'", Sum'>>)
    /\ Print(<<"Pick'", Pick'>>, TRUE)

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* Invariants                                                              *)
---------------------------------------------------------------------------

Inv == TRUE

THEOREM Spec => [](Inv /\ TypeOK)
=============================================================================