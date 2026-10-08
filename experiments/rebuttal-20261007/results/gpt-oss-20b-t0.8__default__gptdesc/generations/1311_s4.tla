--------------------------- MODULE GCD ----------------------------
EXTENDS Naturals

VARIABLES u, v, pc

vars == <<u, v, pc>>

(*--- INITIAL STATE -----------------------------------------------------*)
Init ==
    /\ pc = 0
    /\ u  = 24
    /\ v  ∈ 1..50

(*--- TRANSITION ACTIONS ----------------------------------------------*)

InitStep ==
    /\ pc   = 0
    /\ u'   = 24
    /\ v'   ∈ 1..50
    /\ pc'  = 1

LoopStep ==
    /\ pc   = 1
    /\ u   > 0
    /\ LET uTemp == IF u < v THEN v ELSE u
           vTemp == IF u < v THEN u ELSE v
       IN
          /\ u'  = uTemp - vTemp
          /\ v'  = vTemp
          /\ pc' = 1

DoneStep ==
    /\ pc   = 1
    /\ u    = 0
    /\ u'   = u
    /\ v'   = v
    /\ pc'  = 3

StutterDone ==
    /\ pc   = 3
    /\ u'   = u
    /\ v'   = v
    /\ pc'  = 3

Next == InitStep \/ LoopStep \/ DoneStep \/ StutterDone

(*--- INVARIANTS --------------------------------------------------------*)
Inv ==
    /\ v > 0
    /\ (pc = 3 => u = 0)

(*--- SPECIFICATION -----------------------------------------------------*)
Spec == /\ Init
        /\ [][Next]_vars
        /\ Inv
====================================================================