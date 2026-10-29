--------------------------- MODULE ParamInstance ---------------------------
EXTENDS Naturals

---------------------------- MODULE AbstractOps ----------------------------
EXTENDS Naturals

VARIABLE v

CONSTANT C(_), K

AlwaysHolds(Op(_)) == [](Op(v))

EventuallyHolds(Op(_)) == <>(Op(v))

AlwaysEventually(Op(_)) == []<>(Op(v))

OpLeadsTo(P(_), Q(_)) == P(v) ~> Q(v)

AlwaysC == [](C(v))

AlwaysBelowK == [](v <= K)

ApplyTwice(Op(_), x) == Op(Op(x))
=============================================================================