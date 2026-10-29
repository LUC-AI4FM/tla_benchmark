---------------------------- MODULE Sum ----------------------------
EXTENDS Naturals

CONSTANTS Foo1, Foo2

Sum == Foo1 + Foo2

\* This specification has no state variables. The definitions below are
\* trivial placeholders that satisfy the required module structure.
\* They introduce no transition behavior.

Init == TRUE

Next == TRUE

Spec == Init /\ [][Next]_<<>>

=============================================================================