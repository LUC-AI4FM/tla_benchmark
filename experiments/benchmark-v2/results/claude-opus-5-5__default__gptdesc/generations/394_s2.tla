---------------------------- MODULE PrimingSemantics ----------------------------
(***************************************************************************)
(* A small regression-style test specification about priming semantics.   *)
(* It checks that priming behaves correctly when applied to:               *)
(*   - direct variable references                                          *)
(*   - zero-arity and parameterized operator applications                  *)
(*   - LET-bound names (zero-arity and parameterized)                      *)
(*   - conditional (IF/THEN/ELSE and CASE) expressions                     *)
(* It also checks that LET-bound names are not confused with variables     *)
(* or with top-level operators of similar shape.                           *)
(* TLC's Print and Assert are used to report and check expected behavior. *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 2

VARIABLES x, y

vars == <<x, y>>

(***************************************************************************)
(* Helper operators                                                        *)
(***************************************************************************)
Id(a)      == a
Inc(a)     == a + 1
XPlusOne   == x + 1
SumXY      == x + y
AddX(a)    == a + x
Pick(c, a, b) == IF c THEN a ELSE b

(* A top-level operator whose name could be confused with a LET name *)
z == y

TypeOK ==
    /\ x \in 0..(N - 1)
    /\ y \in 0..(N - 1)

Init ==
    /\ x = 0
    /\ y = 0

Next ==
    (* Assign primed variables first so later primed expressions are defined *)
    /\ x' = (x + 1) % N
    /\ y' = x
    (* Priming a direct variable reference *)
    /\ Assert(x' = (x + 1) % N, "Direct priming of x failed")
    /\ Assert(y' = x, "Direct priming of y failed")
    (* Priming a zero-arity operator: XPlusOne' = x' + 1 *)
    /\ Assert(XPlusOne' = x' + 1, "Priming zero-arity operator failed")
    /\ Assert(SumXY' = x' + y', "Priming SumXY failed")
    (* Priming a parameterized operator application *)
    /\ Assert(Id(x)' = x', "Priming Id(x) failed")
    /\ Assert(Inc(x)' = x' + 1, "Priming Inc(x) failed")
    /\ Assert(Inc(x') = x' + 1, "Inc applied to x' failed")
    (* Priming an operator whose body mentions a variable: AddX(1)' = 1 + x' *)
    /\ Assert(AddX(1)' = 1 + x', "Priming AddX(1) failed")
    (* Argument is unprimed, body variable is primed: AddX(x)' = x' + x' *)
    /\ Assert(AddX(x)' = x' + x', "Priming AddX(x) failed")
    (* LET-bound zero-arity names *)
    /\ LET a == x
           b == x + y
       IN  /\ Assert(a' = x', "Priming LET name a failed")
           /\ Assert(a = x, "Unprimed LET name a failed")
           /\ Assert(b' = x' + y', "Priming LET name b failed")
    (* LET-bound parameterized operator *)
    /\ LET f(v) == v + x
       IN  /\ Assert(f(1)' = 1 + x', "Priming LET operator f(1) failed")
           /\ Assert(f(1) = 1 + x, "Unprimed LET operator f(1) failed")
    (* LET name shadowing confusion: local name w vs top-level z *)
    /\ LET w == x
       IN  /\ Assert(w' = x', "LET name w primed incorrectly")
           /\ Assert(z' = y', "Top-level z primed incorrectly")
    (* LET binding a constant expression: priming has no effect *)
    /\ LET c == N
       IN  Assert(c' = N, "Priming constant LET name failed")
    (* Priming conditional expressions *)
    /\ Assert((IF x = 0 THEN y ELSE x)' = IF x' = 0 THEN y' ELSE x',
              "Priming IF/THEN/ELSE failed")
    /\ Assert(Pick(x = 0, y, x)' = Pick(x' = 0, y', x'),
              "Priming Pick operator failed")
    /\ Assert((CASE x = 0 -> y [] OTHER -> x + 1)'
                = (CASE x' = 0 -> y' [] OTHER -> x' + 1),
              "Priming CASE failed")
    (* Report the transition *)
    /\ PrintT(<<"x", x, "x'", x', "y", y, "y'", y'>>)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Trivial invariant                                                       *)
(***************************************************************************)
Inv == TRUE

=============================================================================