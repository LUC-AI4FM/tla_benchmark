---------------------------- MODULE Github1161 ----------------------------
EXTENSIONS Naturals

VARIABLE s

CONSTANT Op(_), Op2(_)

vars == <<s>>

Test(n) == TRUE

Test2(n) == n \in 0..8

RECURSIVE Rec(_)
Rec(n) == IF n <= 0 THEN TRUE ELSE Rec(n - 1)

-----------------------------------------------------------------------------
(* Wrapper operators (the abstract module's definitions, inlined)           *)

AbsProperty(P(_)) == [](P(s))

AbsDouble(P(_)) == AbsProperty(P)

AbsStateOp(n) == n \in 0..8

AbsStateProperty == AbsProperty(AbsStateOp)

-----------------------------------------------------------------------------

Init == s = 0

Next == s' = IF s < 8 THEN s + 1 ELSE 0

SPEC == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

Property == AbsProperty(Test)

Double == AbsDouble(Test)

StateProperty == [](s \in 0..8)

PropertyE == AbsStateProperty

PropertyF == AbsDouble(Test2)

PropertyG == AbsDouble(Op)

PropertyH == AbsDouble(Rec)

Tautology == (s = 0) ~> TRUE

ViolatedOp(n) == n < 5

PropertyViolated == AbsDouble(ViolatedOp)

=============================================================================