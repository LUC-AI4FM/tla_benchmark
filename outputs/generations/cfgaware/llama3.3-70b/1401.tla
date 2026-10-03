---------------------------- MODULE Counter --------------------------------
EXTENDS Integers

CONSTANT None

VARIABLE outerX

Inner == INSTANCE InnerModule WITH x <- outerX

Spec == /\ outerX = 0
        /\ [][Next]_outerX
        /\ WF_vars(Inner!Step, outerX)

Prop == <> (outerX = 3)

Next == IF Inner!Enabled THEN Inner!Step ELSE UNCHANGED outerX

==================================