------------------------------ MODULE TwoStateCycle ------------------------------
EXTENDS Sequences

CONSTANT MAX_LOG_LENGTH

VARIABLES state, log

(* Initial condition: start in state A with an empty history log *)
Init == 
  /\ state = "A"
  /\ log = <<>>

(* Next action: cycle between states A and B while keeping the log within bounds *)
Next ==
  /\ Len(log) < MAX_LOG_LENGTH
  /\ LET nextState == IF state = "A" THEN "B" ELSE "A"
     IN
        state' = nextState
        /\ log' = Append(log, nextState)

(* State constraint bounding the length of the history log *)
StateConstraint == Len(log) <= MAX_LOG_LENGTH

(* Full specification with weak fairness on Next and the state constraint *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ []StateConstraint

(* Liveness property claiming eventual reachability of Done *)
EventuallyDone == <> (state = "Done")

ASSERT EventuallyDone
=============================================================================