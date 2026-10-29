---------------------------- MODULE PrimingTest ----------------------------
(***************************************************************************)
(* A small regression-style specification exercising the semantics of     *)
(* priming in TLA+ expressions: priming of direct variable references,    *)
(* priming of operator applications, priming of LET-bound names and LET   *)
(* expressions, and priming of conditional (IF/THEN/ELSE) expressions.    *)
(* TLC's Print and Assert are used to check the expected behavior. The    *)
(* invariant is trivial: Inv == TRUE.                                     *)
(***************************************************************************)
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

---------------------------------------------------------------------------
(* Helper operators                                                         *)
---------------------------------------------------------------------------

\* Identity on its argument (argument may or may not mention variables)
Id(a) == a

\* Increment of its argument
Inc(a) == a + 1

\* Zero-argument operator whose body is a variable reference
GetX == x

\* Operator mixing a variable in its body with a parameter
SumWith(a) == x + a

\* Operator whose body is a conditional over variables
Cond == IF x = 0 THEN y ELSE x

\* Constant-valued operator (priming has no effect)
Seven == 7

---------------------------------------------------------------------------

TypeOK == x \in 0..2 /\ y \in 0..2

Init ==
    /\ x = 0
    /\ y = 0

Next ==
    /\ x' = (x + 1) % 3
    /\ y' = x
    \* Direct variable references
    /\ Assert(x' = (x + 1) % 3,
              "Direct priming of variable x failed")
    /\ Assert(y' = x,
              "Direct priming of variable y failed")
    \* Priming of zero-argument operator applications
    /\ Assert(GetX' = x',
              "Priming of GetX should equal x'")
    /\ Assert(Seven' = 7,
              "Priming of a constant operator should be a no-op")
    \* Priming of operator applications with arguments:
    \* Op(e)' primes everything, both the body and the argument
    /\ Assert(Id(x)' = x',
              "Id(x)' should equal x'")
    /\ Assert(Id(x') = x',
              "Id(x') should equal x'")
    /\ Assert(Inc(x)' = x' + 1,
              "Inc(x)' should equal x' + 1")
    /\ Assert(SumWith(y)' = x' + y',
              "SumWith(y)' should equal x' + y'")
    \* Unprimed application with a primed argument: only the argument is primed
    /\ Assert(SumWith(y') = x + y',
              "SumWith(y') should equal x + y'")
    \* LET expressions: priming a LET-bound name primes its definition
    /\ Assert(LET z == x IN z' = x',
              "Priming LET-bound z == x should equal x'")
    /\ Assert(LET z == x IN z = x,
              "Unprimed LET-bound z == x should equal x")
    /\ Assert((LET z == x + y IN z)' = x' + y',
              "Priming a whole LET expression should prime its body")
    /\ Assert(LET c == 3 IN c' = 3,
              "Priming a constant LET-bound name should be a no-op")
    /\ Assert(LET w(a) == a + x IN w(y)' = y' + x',
              "Priming a LET-defined operator application primes all")
    /\ Assert(LET w(a) == a + x IN w(y') = y' + x,
              "LET-defined operator with primed arg only primes the arg")
    \* Conditional branches
    /\ Assert(Cond' = IF x' = 0 THEN y' ELSE x',
              "Priming Cond should prime the condition and both branches")
    /\ Assert((IF x = 0 THEN y ELSE x)' = (IF x' = 0 THEN y' ELSE x'),
              "Priming an IF expression should prime all subexpressions")
    /\ Assert((IF x' = 0 THEN y ELSE x) = (IF x' = 0 THEN y ELSE x),
              "Conditional on primed test with unprimed branches")
    /\ PrintT(<<"step", x, y, "->", x', y'>>)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

---------------------------------------------------------------------------
(* Properties                                                               *)
---------------------------------------------------------------------------

Inv == TRUE

\* Liveness: x keeps cycling, so it eventually returns to 0 infinitely often
XCycles == []<>(x = 0)

=============================================================================