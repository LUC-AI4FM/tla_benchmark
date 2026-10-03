MODULE PlusCalASTTranslation

VARIABLES Object, Any

Init ==
  /\ Object = <<>>
  /\ Any   = <<>>

Next ==
  UNCHANGED <<Object, Any>>

Spec ==
  Init /\ [][Next]_<<Object, Any>>

Termination == FALSE

====