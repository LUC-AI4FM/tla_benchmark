---- MODULE PrimeTest ----
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Bar(a) == a

Foo(a) == a + y

FooBar(a) == x + a

Init == /\ x = 1
        /\ y = 3

Ok(n) == PrintT(<<"Test", n, "OK">>)
Fail(n) == Assert(FALSE, <<"Test", n, "failed">>)
Check(n, cond) == IF cond THEN Ok(n) ELSE Fail(n)

Next ==
  \/ /\ x = 1
     /\ x' = 2
     /\ y' = y
     /\ Check(1, Bar(x') = 2)
  \/ /\ x = 1
     /\ x' = 2
     /\ y' = y
     /\ Check(2, Bar(x)' = 2)
  \/ /\ x = 1
     /\ x' = 2
     /\ y' = y
     /\ Check(3, Foo(x)' = 5)
  \/ /\ x = 1
     /\ x' = 2
     /\ y' = y
     /\ Check(4, Foo(x') = 5)
  \/ /\ x = 1
     /\ x' = 2
     /\ y' = y
     /\ Check(5, FooBar(x)' = 4)
  \/ /\ x = 1
     /\ x' = 2
     /\ y' = y
     /\ Check(6, FooBar(x') = 3)
  \/ /\ x = 1
     /\ x' = 2
     /\ y' = y
     /\ Check(7, FooBar(x)' # FooBar(x'))
  \/ /\ x = 1
     /\ x' = 2
     /\ y' = y
     /\ LET z == x IN Check(8, z' = 2)
  \/ /\ x = 1
     /\ x' = 2
     /\ y' = y
     /\ LET z == x + y IN Check(9, (z)' = 5 /\ z = 4)
  \/ /\ x = 1
     /\ x' = 2
     /\ y' = y
     /\ LET G(a) == a + x IN Check(10, G(y)' = 5 /\ G(y') = 4)
  \/ /\ x = 1
     /\ x' = 2
     /\ y' = y
     /\ LET w == x' IN Check(11, w = 2)
  \/ /\ x = 1
     /\ x' = 2
     /\ y' = y
     /\ LET H(a) == FooBar(a) IN Check(12, H(x)' = 4 /\ H(x') = 3)
  \/ UNCHANGED vars

Inv == TRUE

Spec == Init /\ [][Next]_vars
====