---------------------------- MODULE ParamInstance ----------------------------
EXTENDS Naturals

---------------------------- MODULE AbstractOps ----------------------------
CONSTANTS F(_), G(_, _), K
VARIABLE v

AlwaysF        == [] F(v)
EventuallyF    == <> F(v)
AlwaysGK       == [] G(v, K)
StepG          == [][G(v, v')]_v
InfOftenF      == []<> F(v)
FLeadsToGK     == F(v) ~> G(v, K)
=============================================================================