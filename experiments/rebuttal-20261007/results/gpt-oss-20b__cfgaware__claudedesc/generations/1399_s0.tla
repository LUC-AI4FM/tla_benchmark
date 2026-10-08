------------------------------ MODULE Github715 ------------------------------
\* Minimal TLA+ specification modeling a Boolean variable that alternates between
\* TRUE and FALSE on each non‑stuttering step.
\*
\* The module defines the following names so that the model‑checking configuration
\* can bind to them:
\*   - Spec  : the complete temporal specification (initial condition + stuttering‑tolerant Next)
\*   - Prop  : a property asserting that x holds at all times
\*   - Prop2 : an equivalent property written explicitly as x = TRUE
\*   - Prop3 : trivially TRUE
\*   - SpecVar: an alias for the variable x

VARIABLE x

Init == x = TRUE

Next == x' = ~x

StutterStep == x' = x

Spec == Init /\ [] (Next \/ StutterStep)

Prop == [](x)

Prop2 == [](x = TRUE)

Prop3 == TRUE

SpecVar == x
=============================================================================