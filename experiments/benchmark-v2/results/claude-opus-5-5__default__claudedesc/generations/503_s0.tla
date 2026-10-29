------------------------------ MODULE Consensus ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Values

VARIABLE chosen

vars == <<chosen>>

-----------------------------------------------------------------------------
TypeOK == /\ chosen \subseteq Values
          /\ IsFiniteSet(chosen)

Init == chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Values : chosen' = {v}

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
ConsistencyInv == Cardinality(chosen) \leq 1

THEOREM Invariance == Spec => [](TypeOK /\ ConsistencyInv)

-----------------------------------------------------------------------------
LiveSpec == Spec /\ WF_vars(Next)

Success == <>(chosen # {})

THEOREM LivenessTheorem == LiveSpec => Success

(***************************************************************************)
(* Model-checking configuration (Consensus.cfg):                           *)
(*                                                                         *)
(*   CONSTANT Values = {v1, v2}                                            *)
(*   SPECIFICATION LiveSpec                                                *)
(*   INVARIANT TypeOK ConsistencyInv                                       *)
(*   PROPERTY Success                                                      *)
(***************************************************************************)
=============================================================================