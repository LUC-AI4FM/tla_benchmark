MODULE TinyClock

VARIABLE clock

Flip(b) ==
  NOT b

Check(c) ==
  IF c = TRUE THEN TRUE
  ELSE IF c = FALSE THEN TRUE
  ELSE Check(Flip(c))

TypeOK == Check(clock)

Init ==
  (* Recursive operator call to Check in Init. *)
  clock = FALSE /\ TypeOK

Next ==
  clock' = Flip(clock)

Inv == TypeOK

Spec == Init /\ [][Next]_clock /\ Inv