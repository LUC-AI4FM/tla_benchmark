---- MODULE SmallTemporalSystem ----
EXTENDS Integers

VARIABLES s

\* @type: (Int) => Bool;
F(var) == var \in {x \in 0..9 : x % 2 = 0}

\* @type: Bool;
Init == s = 0

\* @type: Bool;
Spec == Init /\ [][F(s')]_s

====