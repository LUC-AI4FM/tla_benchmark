---- MODULE ZeroIndexedSequences ----
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS ElementSet

VARIABLES dummy

EmptyZSeq ==
  [i \in 0..-1 |-> i]

IsZSeq(f) ==
  \E n \in Nat : DOMAIN f = 0..(n - 1)

ZLen(zs) ==
  CHOOSE n \in Nat : DOMAIN zs = 0..(n - 1)

ZIndices(zs) ==
  DOMAIN zs

IsValidZIndex(zs, i) ==
  i \in DOMAIN zs

ToZSeq(s) ==
  [i \in 0..(Len(s) - 1) |-> s[i + 1]]

FromZSeq(zs) ==
  [i \in 1..ZLen(zs) |-> zs[i - 1]]

ZSingleton(x) ==
  [i \in 0..0 |-> x]

ZAppend(zs, x) ==
  LET n == ZLen(zs)
  IN  [i \in 0..n |->
         IF i < n THEN zs[i] ELSE x]

ZPrepend(x, zs) ==
  LET n == ZLen(zs)
  IN  [i \in 0..n |->
         IF i = 0 THEN x ELSE zs[i - 1]]

ZConcat(a, b) ==
  LET la == ZLen(a)
      lb == ZLen(b)
  IN  [i \in 0..(la + lb - 1) |->
         IF i < la THEN a[i] ELSE b[i - la]]

ZSubSeq(zs, lo, hi) ==
  IF hi < lo
  THEN EmptyZSeq
  ELSE [i \in 0..(hi - lo) |-> zs[lo + i]]

ZReverse(zs) ==
  LET n == ZLen(zs)
  IN  [i \in 0..(n - 1) |-> zs[(n - 1) - i]]

ZRotateLeft(zs, k) ==
  LET n == ZLen(zs)
  IN  IF n = 0
      THEN zs
      ELSE [i \in 0..(n - 1) |-> zs[(i + (k % n)) % n]]

ZRotateRight(zs, k) ==
  LET n == ZLen(zs)
  IN  IF n = 0
      THEN zs
      ELSE [i \in 0..(n - 1) |-> zs[((i + n) - (k % n)) % n]]

ZEqualPrefix(a, b, n) ==
  \A i \in 0..(n - 1) : a[i] = b[i]

ZCommonPrefixLen(a, b) ==
  LET la == ZLen(a)
      lb == ZLen(b)
      m == IF la <= lb THEN la ELSE lb
  IN  CHOOSE n \in 0..m :
        /\ ZEqualPrefix(a, b, n)
        /\ \/ n = m
           \/ a[n] # b[n]

ZLexLT(a, b, LT) ==
  LET la == ZLen(a)
      lb == ZLen(b)
      m == IF la <= lb THEN la ELSE lb
  IN  \/ \E j \in 0..(m - 1) :
            /\ \A i \in 0..(j - 1) : a[i] = b[i]
            /\ <<a[j], b[j]>> \in LT
      \/ /\ la < lb
         /\ \A i \in 0..(la - 1) : a[i] = b[i]

ZLexLE(a, b, LT) ==
  \/ a = b
  \/ ZLexLT(a, b, LT)

Init ==
  dummy = 0

Next ==
  UNCHANGED dummy

Spec ==
  Init /\ [][Next]_<<dummy>>

====