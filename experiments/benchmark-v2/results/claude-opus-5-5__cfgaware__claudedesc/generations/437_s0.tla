---------------------------- MODULE OpArgTest ----------------------------
VARIABLES x, y

vars == <<x, y>>

Init == /\ x = {"a"}
        /\ y = {"a"}

Next == /\ x' = x \cup {"a"}
        /\ y' = y \cup {"b"}

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Higher-order test operators *)

SetOpTest(Op(_), S) == Op(S)

DomainTest(Op(_), f) == Op(f)

BoolOpTest(Op(_), b) == Op(b)

EnabledTest(Op(_), A) == Op(A)

UnchangedTest(Op(_), e) == Op(e)

PrimeTest(Op(_), e) == Op(e)

-----------------------------------------------------------------------------
(* Static tests executed at startup *)

ASSUME
  LET -. S  == S \ {"a"}
      S ^+  == S \ {"b"}
      S ^*  == S \ {"c"}
      S ^#  == S \ {"a", "b"}
  IN  /\ SetOpTest(-., {"a", "b", "c"}) = -. {"a", "b", "c"}
      /\ SetOpTest(-., {"a", "b", "c"}) = {"b", "c"}
      /\ SetOpTest(^+, {"a", "b", "c"}) = {"a", "b", "c"} ^+
      /\ SetOpTest(^+, {"a", "b", "c"}) = {"a", "c"}
      /\ SetOpTest(^*, {"a", "b", "c"}) = {"a", "b", "c"} ^*
      /\ SetOpTest(^*, {"a", "b", "c"}) = {"a", "b"}
      /\ SetOpTest(^#, {"a", "b", "c"}) = {"a", "b", "c"} ^#
      /\ SetOpTest(^#, {"a", "b", "c"}) = {"c"}
      /\ SetOpTest(SUBSET, {"a", "b"}) = SUBSET {"a", "b"}
      /\ SetOpTest(UNION, {{"a"}, {"b"}}) = UNION {{"a"}, {"b"}}
      /\ SetOpTest(UNION, {{"a"}, {"b"}}) = {"a", "b"}
      /\ DomainTest(DOMAIN, [i \in {1, 2} |-> i]) = DOMAIN [i \in {1, 2} |-> i]
      /\ DomainTest(DOMAIN, [i \in {1, 2} |-> i]) = {1, 2}
      /\ BoolOpTest(~, TRUE) = ~TRUE
      /\ BoolOpTest(~, FALSE) = TRUE

-----------------------------------------------------------------------------
(* Tests involving ENABLED, UNCHANGED and prime *)

Invariant == EnabledTest(ENABLED, Next) = ENABLED Next

ImpliedAction == /\ UnchangedTest(UNCHANGED, x)
                 /\ PrimeTest(', y) = y \cup {"b"}
                 /\ PrimeTest(', x) = x

Property == [][ImpliedAction]_vars
=============================================================================