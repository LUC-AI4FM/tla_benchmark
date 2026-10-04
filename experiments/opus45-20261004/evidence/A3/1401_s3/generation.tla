---------------------------- MODULE CounterSystem ----------------------------

EXTENDS Naturals

VARIABLES outerX

-----------------------------------------------------------------------------
(* Inner module defined inline, then instantiated with outerX substituted for x *)

Inner(x) ==
    /\ x < 3
    /\ x' = x + 1

InnerEnabled(x) ==
    x < 3

-----------------------------------------------------------------------------
(* Outer module specification *)

Init ==
    outerX = 0

InnerStep ==
    Inner(outerX)

Next ==
    \/ InnerStep
    \/ (~InnerEnabled(outerX) /\ UNCHANGED outerX)

-----------------------------------------------------------------------------
(* Fairness: Weak fairness on the inner step *)

Fairness ==
    WF_outerX(InnerStep)

-----------------------------------------------------------------------------
(* Full specification with fairness *)

Spec ==
    Init /\ [][Next]_outerX /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariant: outerX is always in valid range *)

TypeInvariant ==
    outerX \in 0..3

SafetyInvariant ==
    outerX >= 0 /\ outerX <= 3

-----------------------------------------------------------------------------
(* Liveness property: outerX eventually reaches 3 *)

LivenessProperty ==
    <>(outerX = 3)

=============================================================================