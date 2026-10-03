---------------------------- MODULE OuterModule ----------------------------
EXTENDS Integers, Sequences
VARIABLES result, seq

InnerModule == INSTANCE Inner WITH result \= r, seq \= s

Spec == /\ result = 0
        /\ seq = <<>>
        /\ [][NextStep_r_s \/ (r' = r /\ s' = s)]

NextStep_r_s == InnerModule!NextStep_r_s

THEOREM SpecRunsToEnd == <>[]<>(~Enabled (<NextStep_r_s>))
=============================================================================