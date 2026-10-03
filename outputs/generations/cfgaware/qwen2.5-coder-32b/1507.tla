------------------------------- MODULE ClockSystem -------------------------------

VARIABLES clock

CONSTANTS TRUE FALSE

(*--algorithm ClockSystem
variables clock \in {TRUE, FALSE}
begin
    while TRUE do
        with (clock := ~clock)
    end while
end algorithm*)

TypeOK == clock \in {TRUE, FALSE}

Init == /\ TypeOK
        /\ clock = TRUE  (* TLC will cover this initial state and the recursive call in Check *)

Next == \/ /\ clock = TRUE
            /\ clock' = FALSE
         \/ /\ clock = FALSE
            /\ clock' = TRUE

Check(x) == \/ x = TRUE
          \/ x = FALSE
          \/ Check(~x)  \* Recursive call to demonstrate TLC coverage

Flip(x) == ~x

=============================================================================