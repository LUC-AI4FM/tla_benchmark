------------------------------- MODULE MutexLock -------------------------------

EXTENDS Integers, TLC, Sequences

CONSTANTS P1, P2
VARIABLES lock, loc

Init == 
  /\ lock = FALSE
  /\ loc = [P1 -> "non-critical", P2 -> "non-critical"]

Next ==
  \/ /\ loc[P1] = "non-critical"
     /\ lock = FALSE
     /\ loc' = [loc EXCEPT ![P1] = "l1"]
     /\ UNCHANGED lock
  \/ /\ loc[P1] = "l1"
     /\ lock = FALSE
     /\ lock'
     /\ loc' = [loc EXCEPT ![P1] = "cs"]
  \/ /\ loc[P1] = "cs"
     /\ loc' = [loc EXCEPT ![P1] = "non-critical"]
     /\ lock' = FALSE
  \/ /\ loc[P2] = "non-critical"
     /\ lock = FALSE
     /\ loc' = [loc EXCEPT ![P2] = "l1"]
     /\ UNCHANGED lock
  \/ /\ loc[P2] = "l1"
     /\ lock = FALSE
     /\ lock'
     /\ loc' = [loc EXCEPT ![P2] = "cs"]
  \/ /\ loc[P2] = "cs"
     /\ loc' = [loc EXCEPT ![P2] = "non-critical"]
     /\ lock' = FALSE

Spec == 
  Init /\ [][Next]_<<lock, loc>>

MutualExclusion ==
  \/ lock = FALSE
  \/ (loc[P1] # "cs") \/ (loc[P2] # "cs")

TypeInvariant ==
  /\ lock \in {FALSE, TRUE}
  /\ loc[P1] \in {"non-critical", "l1", "cs"}
  /\ loc[P2] \in {"non-critical", "l1", "cs"}

SpecWithInvariants ==
  Spec /\ WF_[Next]_<<lock, loc>> 
       /\ []TypeInvariant
       /\ [](MutualExclusion)

LivenessProperty ==
  <>[](loc[P1] = "l1") => <>[] (loc[P1] = "cs")

CompleteSpec ==
  SpecWithInvariants /\ LivenessProperty

=============================================================================