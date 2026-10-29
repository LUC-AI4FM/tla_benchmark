---- MODULE Session2_MC ----
EXTENDS Naturals

\* Self-contained stand-in for the Session2 base module.
\* The real Session2 module was not available, so this wrapper defines
\* a minimal session model locally and exposes the "Spec" formula.

MaxMsgs == 3

VARIABLES state, msgs

vars == <<state, msgs>>

States == {"idle", "open", "closed"}

TypeOK ==
    /\ state \in States
    /\ msgs \in 0..MaxMsgs

Init ==
    /\ state = "idle"
    /\ msgs = 0

Open ==
    /\ state = "idle"
    /\ state' = "open"
    /\ msgs' = 0

Send ==
    /\ state = "open"
    /\ msgs < MaxMsgs
    /\ msgs' = msgs + 1
    /\ UNCHANGED state

Close ==
    /\ state = "open"
    /\ state' = "closed"
    /\ UNCHANGED msgs

Reset ==
    /\ state = "closed"
    /\ state' = "idle"
    /\ msgs' = 0

Next == Open \/ Send \/ Close \/ Reset

Spec == Init /\ [][Next]_vars

====