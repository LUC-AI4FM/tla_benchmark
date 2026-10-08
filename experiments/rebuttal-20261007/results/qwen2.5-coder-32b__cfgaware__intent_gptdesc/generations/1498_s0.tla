---- MODULE ToggleSystem ----

VARIABLES state

(* --algorithm ToggleSystem
variables state \in BOOLEAN;

begin
    Init;
    while TRUE do
        either
            /\ \/ state' = ~state
               /\ \/ state = FALSE -> state' = TRUE
                  /\ state = TRUE  -> state' = FALSE
        or
            /\ \/ state' = ~state
               /\ \/ state = FALSE -> state' = TRUE
                  /\ state = TRUE  -> state' = FALSE
        end either;
    od;
end algorithm *)

CONSTANTS Init, Next

Init == state = FALSE

Next ==
    \/ \/ state' = ~state
       /\ \/ state = FALSE -> state' = TRUE
          /\ state = TRUE  -> state' = FALSE
    \/ \/ state' = ~state
       /\ \/ state = FALSE -> state' = TRUE
          /\ state = TRUE  -> state' = FALSE

Spec ==
    Init /\ [][Next]_<<state>>

Liveness == <>[](\/ state' = ~state)

Safety ==
    \A s \in BOOLEAN : \A t \in BOOLEAN :
        \/ s # t => (s' = t) => (t = ~s)
    
Fairness ==
    WF_next(<<state>>)

Correctness ==
    Spec /\ Liveness /\ Safety /\ Fairness
         /\ []<>(state = FALSE) /\ []<>(state = TRUE)
         /\ [](\/ state' = ~state)

====