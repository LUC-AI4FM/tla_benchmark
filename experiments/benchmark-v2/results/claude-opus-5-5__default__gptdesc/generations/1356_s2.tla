---- MODULE ParamOpInstance ----
EXTENDS Naturals

---- MODULE AbstractOps ----
CONSTANT P(_), Q
VARIABLE x

AlwaysP == [](P(x))

AlwaysHolds(G(_)) == [](G(x))

EventuallyQ == <>(x = Q)

QLeadsToQ == (x = Q) ~> (x = Q)
====