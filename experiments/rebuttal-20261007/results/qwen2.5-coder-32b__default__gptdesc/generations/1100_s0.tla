------------------------------- MODULE MutualExclusionLock -------------------------------
EXTENDS Integers, TLC

CONSTANTS P1, P2

VARIABLES lock, loc1, loc2

Init == 
  /\ lock = FALSE
  /\ loc1 \in {"nc", "l1", "cs"}
  /\ loc2 \in {"nc", "l2", "cs"}
  /\ (loc1 = "nc" \/ loc1 = "l1")
  /\ (loc2 = "nc" \/ loc2 = "l2")

Next == 
  \/ /\ loc1 = "nc"
     /\ lock = FALSE
     /\ loc1' = "l1"
     /\ UNCHANGED <<lock, loc2>>
  \/ /\ loc1 = "l1"
     /\ lock = FALSE
     /\ lock'
     /\ loc1' = "cs"
     /\ UNCHANGED loc2
  \/ /\ loc1 = "cs"
     /\ lock'
     /\ loc1' = "nc"
     /\ UNCHANGED loc2
  \/ /\ loc2 = "nc"
     /\ lock = FALSE
     /\ loc2' = "l2"
     /\ UNCHANGED <<lock, loc1>>
  \/ /\ loc2 = "l2"
     /\ lock = FALSE
     /\ lock'
     /\ loc2' = "cs"
     /\ UNCHANGED loc1
  \/ /\ loc2 = "cs"
     /\ lock'
     /\ loc2' = "nc"
     /\ UNCHANGED loc1

Spec == 
  Init /\ [][Next]_<<lock, loc1, loc2>> /\ WF_[Next]_<<lock, loc1, loc2>>

MutualExclusion ==
  \/ loc1 # "cs" \/ loc2 # "cs"

LivenessP1 ==
  <>[](loc1 = "l1") => <>(loc1 = "cs")

SpecWithProperties == 
  Spec /\ []MutualExclusion /\ LivenessP1

=============================================================================