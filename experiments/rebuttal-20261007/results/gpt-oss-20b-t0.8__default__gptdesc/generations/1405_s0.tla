----------------------------- MODULE Inner -----------------------------
EXTENDS Sequences

VARIABLES r, s

Init ==
    /\ r = 0
    /\ s = <<>>

Step ==
    /\ r = 0
    /\ r' = 1
    /\ s' = SelectSeq(s, \lambda x : x # r')

Next == Step

SpecInner == Init /\ [][Next]_vars
---------------------------------------------------------------------

----------------------------- MODULE Outer -----------------------------
EXTENDS Sequences

VARIABLES R, S

INSTANCE Inner WITH [r -> R, s -> S]

Stutter ==
    /\ R' = R
    /\ S' = S

NextOuter == Step \/ Stutter

Spec ==
    Init
    /\ [][NextOuter]_(<<R,S>>)
    /\ WF_action[Step]
    /\ <> [](~Step)
---------------------------------------------------------------------