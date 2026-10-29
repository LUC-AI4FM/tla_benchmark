---------------------------- MODULE Github136Inner ----------------------------
EXTENDS Naturals

CONSTANTS Foo1, Foo2

Sum == Foo1 + Foo2

Init == TRUE

Next == TRUE

Spec == Init /\ [][Next]_<<>>

=============================================================================