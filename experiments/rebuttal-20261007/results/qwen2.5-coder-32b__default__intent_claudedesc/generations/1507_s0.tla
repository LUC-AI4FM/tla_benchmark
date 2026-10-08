------------------------------- MODULE BooleanClock -------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS ClockInit

VARIABLES clock

(*--algorithm BooleanClock
variables clock;

begin
    Init:
        /\ clock = [rec Nat \o (n) -> IF n = 0 THEN ClockInit ELSE ~rec(n-1)](0)
    next:
        /\ clock' = ~clock
end algorithm;*)

Init == clock = [rec Nat \o (n) -> IF n = 0 THEN ClockInit ELSE ~rec(n-1)](0)

Next == clock' = ~clock

TypeInvariant == [rec Nat \o (n) -> IF n = 0 THEN clock \in {TRUE, FALSE} ELSE rec(n-1)](0)

Spec ==
    /\ Init
    /\ [][Next]_<<clock>>
    /\ WF_next(<<clock>>)
    /\ TypeInvariant

WF_next(vars) == \/ vars = <<>>
                 \/ \E x \in DOMAIN vars : WF_vars[vars EXCEPT ![x] = UNCHANGED vars[x]]

================================================================================