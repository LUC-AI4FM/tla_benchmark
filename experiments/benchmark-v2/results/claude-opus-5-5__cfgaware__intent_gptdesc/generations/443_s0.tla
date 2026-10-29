---------------------------- MODULE EnabledChoice ----------------------------
EXTENDS Integers

VARIABLE u

vars == <<u>>

-----------------------------------------------------------------------------
(* Abstract environment steps on the single integer state u.               *)
-----------------------------------------------------------------------------

\* No-op step: the integer is left unchanged.
NoOp == u' = u

\* Self-update step: a new value computed from the current value.
\* (Kept modular so the state space stays finite for model checking.)
SelfUpdate == u' = (u * 2) % 4

\* Deterministic increment alternative.
Incr == u' = (u + 1) % 4

\* Swap-like / symmetric transition: two values a and b in the guard
\* expression are exchanged conceptually. Here u takes the value of one
\* member of a symmetric pair in which u is the other member.
Swap == \E a, b \in {u, (u + 1) % 4} :
           /\ a # b
           /\ a = u
           /\ u' = b

-----------------------------------------------------------------------------
(* Enabledness of compound choices.                                         *)
-----------------------------------------------------------------------------

\* G: a transition is allowed when at least one of the alternatives
\* (no-op, self-update, symmetric exchange) is enabled.
G == ENABLED (NoOp \/ SelfUpdate \/ Swap)

\* H: composite guarded action. It conjoins a stuttering step on the main
\* state with the enabledness of a compound choice in which one of the
\* alternatives is the deterministic increment.
H == /\ UNCHANGED u
     /\ ENABLED (Incr \/ NoOp \/ Swap)

-----------------------------------------------------------------------------
(* System specification.                                                    *)
-----------------------------------------------------------------------------

Init == u = 0

Next == \/ NoOp
        \/ SelfUpdate
        \/ Swap
        \/ Incr
        \/ H

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Incr)

-----------------------------------------------------------------------------
(* Properties.                                                              *)
-----------------------------------------------------------------------------

\* Safety: every reached state is an integer in the legal range.
TypeOK == /\ u \in Int
          /\ u \in 0..3

\* Nontrivial enabledness semantics: the disjunctive enabledness predicate
\* holds in every state, and so does the enabledness of the composite
\* stuttering-guarded action.
EnabledOK == /\ G
             /\ ENABLED H
             /\ (ENABLED (NoOp \/ SelfUpdate \/ Swap))
                  = ((ENABLED NoOp) \/ (ENABLED SelfUpdate) \/ (ENABLED Swap))

\* Liveness: if the increment is continuously enabled, it eventually occurs.
IncrLiveness == (<>[](ENABLED <<Incr>>_vars)) => []<><<Incr>>_vars

\* H steps never change u.
HStutters == [][H => UNCHANGED u]_vars

THEOREM Spec => []TypeOK
THEOREM Spec => []EnabledOK
THEOREM Spec => IncrLiveness
=============================================================================