---- MODULE ZeroIndexedSequences ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS ElemSet, ElemLess(_,_)

VARIABLES dummy

vars == <<dummy>>

Min(a, b) ==
    IF a <= b THEN a ELSE b

ZDomain(n) ==
    0..(n - 1)

IsZSeq(s) ==
    \E n \in Nat : DOMAIN s = ZDomain(n)

ZSeqs(S) ==
    UNION { [ZDomain(n) -> S] : n \in Nat }

IsZSeqOver(s, S) ==
    /\ IsZSeq(s)
    /\ \A i \in DOMAIN s : s[i] \in S

ZLen(s) ==
    CHOOSE n \in Nat : DOMAIN s = ZDomain(n)

ZIndices(s) ==
    ZDomain(ZLen(s))

IsZIndex(s, i) ==
    i \in ZIndices(s)

ZEmpty ==
    [i \in {} |-> i]

ZSingleton(x) ==
    [i \in 0..0 |-> x]

ZFromSeq(q) ==
    [i \in ZDomain(Len(q)) |-> q[i + 1]]

ZToSeq(s) ==
    [i \in 1..ZLen(s) |-> s[i - 1]]

ZHead(s) ==
    s[0]

ZLast(s) ==
    s[ZLen(s) - 1]

ZTail(s) ==
    [i \in ZDomain(ZLen(s) - 1) |-> s[i + 1]]

ZAppend(s, x) ==
    LET n == ZLen(s)
    IN [i \in ZDomain(n + 1) |->
            IF i = n THEN x ELSE s[i]]

ZConcat(a, b) ==
    LET la == ZLen(a)
        lb == ZLen(b)
    IN [i \in ZDomain(la + lb) |->
            IF i < la THEN a[i] ELSE b[i - la]]

ZPrefix(s, n) ==
    [i \in ZDomain(n) |-> s[i]]

ZDrop(s, n) ==
    [i \in ZDomain(ZLen(s) - n) |-> s[i + n]]

ZSubSeq(s, lo, hi) ==
    [i \in ZDomain(hi - lo + 1) |-> s[lo + i]]

ZReverse(s) ==
    LET n == ZLen(s)
    IN [i \in ZDomain(n) |-> s[n - 1 - i]]

ZRotateLeft(s, k) ==
    LET n == ZLen(s)
    IN IF n = 0
       THEN s
       ELSE [i \in ZDomain(n) |-> s[(i + k) % n]]

ZRotateRight(s, k) ==
    LET n == ZLen(s)
    IN IF n = 0
       THEN s
       ELSE [i \in ZDomain(n) |-> s[(i - (k % n) + n) % n]]

ZPrefixEqual(a, b, n) ==
    \A i \in ZDomain(n) : a[i] = b[i]

ElemLessIrreflexiveOn(S) ==
    \A x \in S : ~ElemLess(x, x)

ElemLessTransitiveOn(S) ==
    \A x, y, z \in S :
        /\ ElemLess(x, y)
        /\ ElemLess(y, z)
        => ElemLess(x, z)

ElemLessTotalOn(S) ==
    \A x, y \in S :
        x # y => \/ ElemLess(x, y)
                  \/ ElemLess(y, x)

ElemLessStrictTotalOrderOn(S) ==
    /\ ElemLessIrreflexiveOn(S)
    /\ ElemLessTransitiveOn(S)
    /\ ElemLessTotalOn(S)

ZLexLess(a, b) ==
    LET la == ZLen(a)
        lb == ZLen(b)
        m == Min(la, lb)
    IN \/ \E j \in ZDomain(m) :
              /\ ZPrefixEqual(a, b, j)
              /\ ElemLess(a[j], b[j])
       \/ /\ ZPrefixEqual(a, b, m)
          /\ la < lb

ZLexLeq(a, b) ==
    \/ a = b
    \/ ZLexLess(a, b)

Init ==
    TRUE

Next ==
    UNCHANGED vars

Spec ==
    Init /\ [][Next]_vars

====