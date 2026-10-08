---------------------------- MODULE GCD ----------------------------------
EXTENDS Integers

CONSTANT FirstInput, MaxSecondInput

VARIABLE secondInput, currentPair, terminated

Init ==
  /\ secondInput \in 1..MaxSecondInput
  /\ currentPair = <<FirstInput, secondInput>>
  /\ terminated = FALSE

Next ==
  IF ~terminated THEN
    /\ LET pair == currentPair IN
      IF pair[1] = 0 THEN
        /\ currentPair' = pair
        /\ terminated' = TRUE
      ELSEIF pair[2] = 0 THEN
        /\ currentPair' = pair
        /\ terminated' = TRUE
      ELSE
        /\ IF pair[1] < pair[2]
             THEN currentPair' = <<pair[2] - pair[1], pair[1]>>
             ELSE currentPair' = <<pair[1], pair[2]>>
        /\ terminated' = FALSE
  ELSE
    /\ currentPair' = currentPair
    /\ terminated' = TRUE

Spec == Init /\ [][Next]_<<currentPair, terminated>>

THEOREM Spec => []~(currentPair[1] < 0 \/ currentPair[2] < 0)
THEOREM Spec => <>terminated

=============================================================================