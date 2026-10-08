------------------------------- MODULE BooleanClock -------------------------------

VARIABLE clock

(*--algorithm BooleanClock
variables clock;

Init == 
    /\ clock = FALSE
    /\ InitHelper(clock)

Next ==
    \/ /\ clock = TRUE
       /\ clock' = FALSE
    \/ /\ clock = FALSE
       /\ clock' = TRUE

TypeOK ==
    TypeOKHelper(clock)

InitHelper(c) == c \in {TRUE, FALSE}

TypeOKHelper(c) == c \in BOOLEAN

end algorithm *)

=============================================================================