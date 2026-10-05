-------------------------------- MODULE LockHS --------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

VARIABLES pc, x, h_turn, s

\* Define Stuttering values
top == "top"
s1 == "s1"
s2 == "s2"
bot == "bot"

Stuttering == {top, s1, s2, bot}

\* Process set
Procs == 1..N

\* PC locations
Locations == {"l0", "l1", "cs", "l2"}

\* ============================================================================