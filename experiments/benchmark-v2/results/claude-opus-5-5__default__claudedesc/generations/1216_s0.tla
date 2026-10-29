---- MODULE PrimingTest ----
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

TypeOK == x \in Nat /\ y \in Nat

Init == /\ x = 1
        /\ y = 3

Bar(a) == a

Foo(a) == a + y

FooBar(a) == a + x

Baz(a, b) == a * x + b

Test1 ==
  /\ x = 1
  /\ x' = 2
  /\ y' = y
  /\ IF Bar(x') = 2 /\ Bar(x)' = 2 /\ Bar(x) = 1
       THEN Print("Test 1 OK", TRUE)
       ELSE Assert(FALSE, "Test 1 Failed")

Test2 ==
  /\ x = 1
  /\ x' = 2
  /\ y' = y
  /\ IF Foo(x)' = 5 /\ Foo(x') = 5 /\ Foo(x) = 4
       THEN Print("Test 2 OK", TRUE)
       ELSE Assert(FALSE, "Test 2 Failed")

Test3 ==
  /\ x = 1
  /\ x' = 2
  /\ y' = y
  /\ IF FooBar(x)' = 4 /\ FooBar(x') = 3 /\ FooBar(x)' # FooBar(x')
       THEN Print("Test 3 OK", TRUE)
       ELSE Assert(FALSE, "Test 3 Failed")

Test4 ==
  /\ x = 1
  /\ x' = 2
  /\ y' = y
  /\ LET z == x
     IN IF z' = 2 /\ z = 1
          THEN Print("Test 4 OK", TRUE)
          ELSE Assert(FALSE, "Test 4 Failed")

Test5 ==
  /\ x = 1
  /\ x' = 2
  /\ y' = y
  /\ LET w == x + y
     IN IF (w + x)' = 7 /\ w' + x = 6 /\ (w + x) = 5
          THEN Print("Test 5 OK", TRUE)
          ELSE Assert(FALSE, "Test 5 Failed")

Test6 ==
  /\ x = 1
  /\ x' = 2
  /\ y' = y
  /\ IF Baz(y, 1)' = 7 /\ Baz(y', 1) = 4 /\ Baz(x', y') = 7
       THEN Print("Test 6 OK", TRUE)
       ELSE Assert(FALSE, "Test 6 Failed")

Test7 ==
  /\ x = 1
  /\ x' = 2
  /\ y' = y
  /\ LET G(a) == a + x
     IN IF G(y)' = 5 /\ G(y') = 4 /\ G(x)' = 4
          THEN Print("Test 7 OK", TRUE)
          ELSE Assert(FALSE, "Test 7 Failed")

Next == \/ Test1
        \/ Test2
        \/ Test3
        \/ Test4
        \/ Test5
        \/ Test6
        \/ Test7
        \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

Inv == TRUE

THEOREM Spec => []Inv
====