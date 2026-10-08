MODULE SmallSM
EXTENDS Naturals, TLC

VARIABLE x

Init == x = 0

Next == x' = (x + 1) MOD 3

IsOne    == x = 1
Done     == x = 2
Wrapped  == (x = 2 /\ x' = 0)

Spec == Init /\ [] [Next]_<<x>>

CheckCoverage ==
  LET cov == TLCGet("COVERAGE") IN
    /\ cov["IsOne"]   = 1
    /\ cov["Done"]    = 1
    /\ cov["Wrapped"] = 1

CHECK CheckCoverage

END MODULE