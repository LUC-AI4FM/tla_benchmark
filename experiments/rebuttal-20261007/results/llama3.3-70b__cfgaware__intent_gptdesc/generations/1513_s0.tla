---------------------------- MODULE TokenPassingTerminationDetection ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT ProcSet, ColorSet
VARIABLE token, procStatus, localColor, detector

procStatus == [p \in ProcSet |-> "active"]
localColor == [p \in ProcSet |-> FALSE]
token == <<1, TRUE>>  \* process index and color bit
detector == FALSE

TypeInvariant ==
  /\ token \in (ProcSet \X ColorSet)
  /\ procStatus \in [ProcSet -> {"active", "passive"}]
  /\ localColor \in [ProcSet -> BOOLEAN]
  /\ detector \in BOOLEAN

Init ==
  TypeInvariant
  /\ token = <<1, TRUE>>
  /\ procStatus = [p \in ProcSet |-> "active"]
  /\ localColor = [p \in ProcSet |-> FALSE]
  /\ detector = FALSE

Next(p) == 
  \/ \* generate work and become active
    /\ p \in ProcSet
    /\ procStatus' = [procStatus EXCEPT ![p] = "active"]
    /\ UNCHANGED <<token, localColor, detector>>
  \/ \* process work and become passive
    /\ p \in ProcSet
    /\ procStatus' = [procStatus EXCEPT ![p] = "passive"]
    /\ UNCHANGED <<token, localColor, detector>>
  \/ \* change local color bit
    /\ p \in ProcSet
    /\ localColor' = [localColor EXCEPT ![p] = ~localColor[p]]
    /\ UNCHANGED <<token, procStatus, detector>>
  \/ \* forward token to next process
    /\ token[1] = p
    /\ token' = IF p = Max(ProcSet)
                THEN <<Min(ProcSet), token[2]>>
                ELSE <<p + 1, token[2]>>
    /\ UNCHANGED <<procStatus, localColor, detector>>
  \/ \* mark global quiescence and declare termination
    /\ detector' = TRUE
    /\ token' = token
    /\ procStatus' = procStatus
    /\ localColor' = localColor

Next ==
  \E p \in ProcSet : Next(p)

Spec == Init /\ [][Next]_<<token, procStatus, localColor, detector>>

THEOREM Spec => []TypeInvariant

Fairness == 
  \/ \* fairness assumption for token delivery
    WF_(Next)(<<token, procStatus, localColor, detector>>)
  \/ \* fairness assumption for scheduling
    SF_(Next)(<<token, procStatus, localColor, detector>>)

TerminationDetection ==
  <>[]detector = TRUE

THEOREM Spec /\ Fairness => TerminationDetection

IncorrectTermination ==
  <>[]/\ detector = TRUE
       /\ \E p \in ProcSet : procStatus[p] = "active"
  \/ <>[]/\ detector = TRUE
       /\ \E p \in ProcSet : localColor[p] /= token[2]

THEOREM Spec /\ Fairness => []~IncorrectTermination

=============================================================================