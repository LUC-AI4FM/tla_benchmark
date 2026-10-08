MODULE TerminationDetection
EXTENDS Naturals

CONSTANTS ProcSet, MaxMsgs

VARIABLES active, inTransit, detected

(* Type invariant for model checking *)
TypeInvariant == /\ active \in [ProcSet -> BOOLEAN]
                /\ inTransit \in [ProcSet -> 0..MaxMsgs]
                /\ detected \in BOOLEAN

Init == /\ TypeInvariant
        /\ \A p \in ProcSet : active[p] = FALSE
        /\ \A p \in ProcSet : inTransit[p] = 0
        /\ detected = FALSE

Terminated == /\ \A p \in ProcSet : active[p] = FALSE
              /\ \A p \in ProcSet : inTransit[p] = 0

Send ==
  \E src,dest \in ProcSet :
    /\ src /= dest
    /\ active[src] = TRUE
    /\ inTransit[dest] < MaxMsgs
    /\ inTransit' = [inTransit EXCEPT ![dest] = @ + 1]
    /\ UNCHANGED <<active, detected>>

Deliver ==
  \E dest \in ProcSet :
    /\ inTransit[dest] > 0
    /\ inTransit' = [inTransit EXCEPT ![dest] = @ - 1]
    /\ active'   = [active EXCEPT ![dest] = TRUE]
    /\ UNCHANGED <<detected>>

Deactivate ==
  \E p \in ProcSet :
    /\ active[p] = TRUE
    /\ active'   = [active EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<inTransit, detected>>

Detect ==
  /\ detected = FALSE
  /\ Terminated
  /\ detected' = TRUE
  /\ UNCHANGED <<active, inTransit>>

Next == Send \/ Deliver \/ Deactivate \/ Detect

LivenessProp == [] (Terminated /\ ~detected => <> detected)

SafetyInvariant == [] (detected => Terminated)

Spec ==
  Init
  /\ [][Next]_<<active,inTransit,detected>>
  /\ LivenessProp
  /\ Fairness(Next)

THEOREM Safety : Spec => SafetyInvariant
THEOREM Liveness : Spec => LivenessProp