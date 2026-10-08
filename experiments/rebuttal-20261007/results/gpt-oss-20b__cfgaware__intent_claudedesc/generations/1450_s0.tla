------------------------------ MODULE RandomFunctionSample ------------------------------
EXTENDS Naturals, Sequences, Random

CONSTANTS Domain, Codomain, SampleSize

VARIABLE sampleSet

Init ==
  /\ sampleSet = RandomSubset([Domain -> Codomain], SampleSize)

Next ==
  /\ UNCHANGED <<sampleSet>>

Spec == Init /\ [][Next]_<<sampleSet>>

Inv == TRUE

=============================================================================