---------------------------- MODULE Github1161 ----------------------------
EXTENDS Naturals

    ---------------------- MODULE Github1161Abstract ----------------------
    EXTENDS Naturals

    VARIABLE s

    Property(P(_)) == [](P(s))

    Double(P(_)) == Property(P)

    InRange(x) == x \in 0..8

    PropertyE == Property(InRange)
    =======================================================================