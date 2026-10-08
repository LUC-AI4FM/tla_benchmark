----------------------------- MODULE SubsetReasoning -----------------------------
EXTENDS Naturals, Integers, TLC

VARIABLES n, m, SInt, SNat, Consistent

Range(k) == 1..k

NotSubset(A, B) == ~(A \subseteq B)

TypeInv ==
  /\ n \in Nat
  /\ m \in Nat
  /\ SInt \subseteq Int
  /\ SNat \subseteq Nat
  /\ IsFiniteSet(SInt)
  /\ IsFiniteSet(SNat)
  /\ Consistent \in BOOLEAN

SubsetTruths ==
  /\ n <= m
  /\ Range(n) \subseteq Range(m)
  /\ NotSubset(Range(m), Range(n))
  /\ {} \subseteq SInt
  /\ {} \subseteq SNat
  /\ {} \subseteq Range(n)
  /\ {} \subseteq Range(m)
  /\ {} \subseteq {}
  /\ ~({0} \subseteq {})
  /\ SInt \subseteq Int
  /\ SNat \subseteq Nat
  /\ SNat \subseteq Int

ConsistencyInv == Consistent = TRUE

Inv == TypeInv /\ SubsetTruths /\ ConsistencyInv

Init ==
  /\ n = 2
  /\ m = 5
  /\ SInt = {-1, 0, 2}
  /\ SNat = {0, 3}
  /\ Consistent = TRUE

Next ==
  /\ UNCHANGED << n, m, SInt, SNat, Consistent >>

vars == << n, m, SInt, SNat, Consistent >>

Spec == Init /\ [][Next]_vars
=============================================================================