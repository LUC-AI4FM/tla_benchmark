--------------------------- MODULE OperatorArgTest ---------------------------
(***************************************************************************)
(* Tests prefix and postfix operators (built-in and user-defined) passed  *)
(* as arguments to higher-order operators.                                 *)
(***************************************************************************)
EXTENDS Naturals, Sequences, TLC

VARIABLES x, y

vars == <<x, y>>

Init == /\ x = {"a"}
        /\ y = {"a"}

Next == /\ x' = x \cup {"a"}
        /\ y' = y \cup {"b"}

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Higher-order test operators                                             *)
-----------------------------------------------------------------------------

SetOpTest(Op(_), S) == Op(S)

DomainTest(Op(_), f) == Op(f)

BoolOpTest(Op(_), b) == Op(b)

EnabledTest(Op(_)) == Op(Next)

UnchangedTest(Op(_)) == Op(x)

PrimeTest(Op(_)) == Op(y) = y \cup {"b"}

-----------------------------------------------------------------------------
(* Static tests executed at startup                                        *)
-----------------------------------------------------------------------------

ASSUME
  LET -S   == {"a", "b", "c"} \ S
      S^+  == S \ {"a"}
      S^*  == S \ {"b"}
      S^#  == S \ {"c"}
  IN  /\ SetOpTest(-., {"a"}) = -{"a"}
      /\ SetOpTest(-., {"a"}) = {"b", "c"}
      /\ SetOpTest(^+, {"a", "b"}) = {"a", "b"}^+
      /\ SetOpTest(^+, {"a", "b"}) = {"b"}
      /\ SetOpTest(^*, {"a", "b"}) = {"a", "b"}^*
      /\ SetOpTest(^*, {"a", "b"}) = {"a"}
      /\ SetOpTest(^#, {"a", "c"}) = {"a", "c"}^#
      /\ SetOpTest(^#, {"a", "c"}) = {"a"}
      /\ SetOpTest(SUBSET, {"a", "b"}) = SUBSET {"a", "b"}
      /\ SetOpTest(SUBSET, {"a"}) = {{}, {"a"}}
      /\ SetOpTest(UNION, {{"a"}, {"b"}}) = UNION {{"a"}, {"b"}}
      /\ SetOpTest(UNION, {{"a"}, {"b"}}) = {"a", "b"}
      /\ DomainTest(DOMAIN, [i \in {1, 2} |-> i]) = DOMAIN [i \in {1, 2} |-> i]
      /\ DomainTest(DOMAIN, [i \in {1, 2} |-> i]) = {1, 2}
      /\ DomainTest(DOMAIN, <<"a", "b", "c">>) = 1..3
      /\ BoolOpTest(~, FALSE) = ~FALSE
      /\ BoolOpTest(~, FALSE) = TRUE
      /\ BoolOpTest(\lnot, TRUE) = FALSE

-----------------------------------------------------------------------------
(* Dynamic tests                                                           *)
-----------------------------------------------------------------------------

(* Not checked in the configuration due to a known TLC bug with ENABLED    *)
(* passed as an operator argument.                                         *)
Invariant == EnabledTest(ENABLED)

ImpliedAction == /\ UnchangedTest(UNCHANGED)
                 /\ PrimeTest(')

Property == [][ImpliedAction]_vars

=============================================================================