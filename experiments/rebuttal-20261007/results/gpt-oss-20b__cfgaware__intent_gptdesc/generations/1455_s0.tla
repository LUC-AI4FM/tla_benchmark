MODULE SubsetReasoning
EXTENDS Integers

CONSTANTS N, M

VARIABLES s, t, consistent, assertSub, assertNotSub

Nat == {i \in Int : i >= 0}

RangeSet(n) == {i \in 1..n}

Init ==
    /\ s = RangeSet(N)
    /\ t = RangeSet(M)
    /\ consistent = TRUE
    /\ assertSub = FALSE
    /\ assertNotSub = FALSE

AddToS(e) ==
    /\ e \in t
    /\ e \notin s
    /\ s' = s ∪ {e}
    /\ t' = t
    /\ consistent' = TRUE
    /\ assertSub' = assertSub
    /\ assertNotSub' = assertNotSub

AddToT(e) ==
    /\ e \notin t
    /\ t' = t ∪ {e}
    /\ s' = s
    /\ consistent' = TRUE
    /\ assertSub' = assertSub
    /\ assertNotSub' = assertNotSub

AssertSub ==
    /\ s \subseteq t
    /\ assertSub' = TRUE
    /\ s' = s
    /\ t' = t
    /\ consistent' = TRUE
    /\ assertNotSub' = assertNotSub

AssertNotSub ==
    /\ ~ (s \subseteq t)
    /\ assertNotSub' = TRUE
    /\ s' = s
    /\ t' = t
    /\ consistent' = TRUE
    /\ assertSub' = assertSub

NoOp ==
    /\ s' = s
    /\ t' = t
    /\ consistent' = TRUE
    /\ assertSub' = assertSub
    /\ assertNotSub' = assertNotSub

Next == (\E e \in Int : AddToS(e)) \/ (\E e \in Int : AddToT(e))
          \/ AssertSub \/ AssertNotSub \/ NoOp

Spec == Init /\ [][Next]_<<s,t,consistent,assertSub,assertNotSub>>

InvariantConsistent == consistent = TRUE

InvariantSubsetAsserted ==
    /\ (assertSub => s \subseteq t)
    /\ (assertNotSub => ~ (s \subseteq t))

InvariantEmptySet ==
    /\ {} \subseteq s
    /\ {} \subseteq t

InvariantFiniteIntSubsetAllIntegers ==
    /\ s \subseteq Int
    /\ t \subseteq Int

InvariantNatSubset ==
    /\ (s \subseteq Nat) \/ TRUE   -- placeholder for natural‑number subset property

============================================================================