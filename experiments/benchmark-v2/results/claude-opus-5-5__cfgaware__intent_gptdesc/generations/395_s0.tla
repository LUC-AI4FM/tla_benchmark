---------------------------- MODULE TwoMapsStateMachine ----------------------------
EXTENDS Integers, FiniteSets, TLC

(***************************************************************************)
(* Fixed finite domains                                                   *)
(***************************************************************************)
Keys      == {"k1", "k2"}
IntRange  == 0..1
FieldA    == {"x", "y"}
FieldB    == {1, 2}

Rec       == [fa : FieldA, fb : FieldB]

\* Type domains of the two map-like components
IntMapDom == [Keys -> SUBSET IntRange]
RecMapDom == [Keys -> SUBSET Rec]

\* Particular record values used for single-element updates
R1 == [fa |-> "x", fb |-> 1]
R2 == [fa |-> "y", fb |-> 2]

\* Target shape that the second component must never take at a given key
TargetKey   == "k1"
TargetShape == {R1, R2}

VARIABLES intMap, recMap

vars == <<intMap, recMap>>

(***************************************************************************)
(* Type correctness                                                       *)
(***************************************************************************)
TypeOK ==
    /\ intMap \in IntMapDom
    /\ recMap \in RecMapDom
    /\ \A k \in Keys : \A r \in recMap[k] :
           /\ DOMAIN r = {"fa", "fb"}
           /\ r.fa \in FieldA
           /\ r.fb \in FieldB

(***************************************************************************)
(* Initial states: arbitrary allowed mappings (each distinct assignment    *)
(* is a distinct initial state).                                          *)
(***************************************************************************)
Init ==
    /\ intMap \in IntMapDom
    /\ recMap \in RecMapDom

(***************************************************************************)
(* Actions                                                                *)
(***************************************************************************)
Stutter ==
    UNCHANGED vars

UpdateIntMap ==
    /\ intMap' \in IntMapDom
    /\ UNCHANGED recMap

UpdateRecMap ==
    /\ recMap' \in RecMapDom
    /\ UNCHANGED intMap

\* Specific single-element updates for particular record values
SetSingleR1 ==
    /\ \E k \in Keys : recMap' = [recMap EXCEPT ![k] = {R1}]
    /\ UNCHANGED intMap

SetSingleR2 ==
    /\ \E k \in Keys : recMap' = [recMap EXCEPT ![k] = {R2}]
    /\ UNCHANGED intMap

AddRecord ==
    /\ \E k \in Keys, r \in {R1, R2} :
           recMap' = [recMap EXCEPT ![k] = @ \cup {r}]
    /\ UNCHANGED intMap

Next ==
    \/ Stutter
    \/ UpdateIntMap
    \/ UpdateRecMap
    \/ SetSingleR1
    \/ SetSingleR2
    \/ AddRecord

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants                                                             *)
(***************************************************************************)
\* (1) The target entry of the second component never coincides with the
\*     specified subset shape (detects two distinct collection-valued state
\*     descriptions coinciding). This is expected to be violated.
NoCoincide == recMap[TargetKey] # TargetShape

\* (2) Type correctness of both components.
Inv ==
    /\ TypeOK
    /\ NoCoincide

=============================================================================