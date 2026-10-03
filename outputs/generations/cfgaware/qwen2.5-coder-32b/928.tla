------------------------------- MODULE HC2 -------------------------------

CONSTANTS hr \* Assuming hr is a constant representing the hour variable

VARIABLES hr

HCini == hr \in 0..11

HCnxt2 == hr' = (hr % 12) + 1

HC2 == HCini /\ [](HCnxt2)_<<hr>>

HC == HCini /\ [](HCnxt)_<<hr>> \* Assuming HCnxt is the original next-state action from HourClock module

THEOREM HC <=> HC2

=============================================================================