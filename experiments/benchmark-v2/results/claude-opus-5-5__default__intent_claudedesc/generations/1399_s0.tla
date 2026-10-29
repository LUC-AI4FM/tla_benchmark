---- MODULE ToggleBoolean ----
EXTENDS Naturals

VARIABLE b

vars == << b >>

TypeOK == b \in BOOLEAN

Init == b = TRUE

Flip == b' = ~b

Next == Flip

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Intentionally violated invariant: b is always TRUE.
\* Fails after the first step, when b becomes FALSE.
AlwaysTrue == [](b = TRUE)

\* State predicate asserting b equals TRUE (violated as an invariant).
IsTrue == b = TRUE

\* Trivially satisfied property.
Trivial == TRUE

TriviallyAlways == []TRUE

\* Expose the variable directly as a property.
BProp == b

\* Additional liveness properties for experimentation (hold under WF).
EventuallyFalse == <>(b = FALSE)

InfinitelyOftenTrue == []<>(b = TRUE)

InfinitelyOftenFalse == []<>(b = FALSE)

THEOREM Spec => []TypeOK
====