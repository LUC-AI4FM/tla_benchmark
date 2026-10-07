---- MODULE SmallTemporal ----
EXTENDS Integers

VARIABLES s

Next(var) ==
  \E n \in 0..1:
    var' = n /\ var' > 0

Init == s = 23

Inv == s # 0

Spec == Init /\ [][Next(s)]_s

====