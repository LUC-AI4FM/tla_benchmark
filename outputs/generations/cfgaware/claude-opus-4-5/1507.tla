---------------------------- MODULE specification ----------------------------

VARIABLE clock

RECURSIVE Check(_)
Check(x) == IF x \in BOOLEAN THEN TRUE ELSE Check(x)

RECURSIVE Flip(_)
Flip(x) == IF x = TRUE THEN FALSE ELSE IF x = FALSE THEN TRUE ELSE Flip(x)

TypeOK == clock \in BOOLEAN

\* Note: The recursive operator Check is called in Init.
\* TLC coverage behavior: The recursive call in Check will show as covered
\* when Init is evaluated, since Check(TRUE) and Check(FALSE) both terminate
\* immediately at the base case (TRUE \in BOOLEAN).
Init == clock \in BOOLEAN /\ Check(clock)

Next == clock' = Flip(clock)

=============================================================================