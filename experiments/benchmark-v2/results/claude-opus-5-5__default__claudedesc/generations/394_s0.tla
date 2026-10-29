---- MODULE PrimeTest ----
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

TypeOK == x \in Nat /\ y \in Nat

Bar(a) == a' = 2

Foo(a) == a = 2

FooBar(a, b) == a = b

LetTest(a) == LET b == a' IN b = 2

Op(a) == a + x

Init == /\ x = 1
        /\ y = 3

Next ==
    \/ /\ x = 1
       /\ x' = 2
       /\ y' = y
       /\ Bar(x)
    \/ /\ IF x = 1
             THEN /\ x' = x + 1
                  /\ PrintT("Test succeeded: x = 1")
             ELSE /\ x' = x + 1
                  /\ PrintT("Branch taken with x # 1")
       /\ y' = y
    \/ UNCHANGED <<x, y>>
    \* Commented-out priming tests:
    \* \/ /\ x = 1 /\ x' = 2 /\ y' = y /\ Foo(x')
    \* \/ /\ x = 1 /\ x' = 2 /\ y' = y /\ (x + y)' = 5
    \* \/ /\ x = 1 /\ x' = 2 /\ y' = y /\ FooBar(x', 2)
    \* \/ /\ x = 1 /\ x' = 2 /\ y' = y /\ LetTest(x)
    \* \/ /\ x = 1 /\ x' = 2 /\ y' = y /\ Op(1)' = 3

Spec == Init /\ [][Next]_vars

Inv == TRUE

====