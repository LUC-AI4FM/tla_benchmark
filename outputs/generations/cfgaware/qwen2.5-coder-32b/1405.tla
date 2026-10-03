---- MODULE OuterModule ----

CONSTANTS Result, Seq

VARIABLES result, seq

\* Inner Module Specification
InnerSpec == INSTANCE InnerModule << [Result <- result, Seq <- seq] >>

Next ==
  \/ InnerSpec.Next
  \/ \A r \in {0, 1}, s \in Seq: /\ result = r
                              /\ seq = s
                              /\ UNCHANGED <<result, seq>>

SpecInit ==
  /\ result = 0
  /\ seq = <<0, 1, 2, 3, 4>>

Spec == SpecInit /\ [][Next]_<<result, seq>>

WF_Spec ==
  WF_next(InnerSpec.Next)

SpecRunsToEnd ==
  <>[]<>(\A r \in {0, 1}, s \in Seq: result = r /\ seq = s /\ ~InnerSpec.Enabled)

====