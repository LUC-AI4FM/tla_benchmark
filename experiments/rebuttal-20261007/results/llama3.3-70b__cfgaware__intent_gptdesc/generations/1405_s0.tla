---------------------------- MODULE TwoComponentSystem ----------------------------
EXTENDS Integers, Sequences

CONSTANT InitialSequence, ResultValue
VARIABLE sequence, result

InnerServiceEnabled == result = 0 /\ ResultValue \in Seq(sequence)

InnerService ==
  /\ result' = ResultValue
  /\ sequence' = [x \in sequence | x # ResultValue]
  /\ UNCHANGED << >>

StutterStep == 
  /\ InnerServiceEnabled = FALSE
  /\ UNCHANGED sequence
  /\ UNCHANGED result

Next == InnerServiceEnabled => InnerService <> StutterStep

Spec ==
  /\ (sequence = InitialSequence) /\ (result = 0)
  /\ [][Next]_<<sequence, result>>
  /\ WF_<<sequence, result>>(InnerService)

THEOREM SpecRunsToEnd == Spec => <>([]InnerServiceEnabled = FALSE)
=============================================================================