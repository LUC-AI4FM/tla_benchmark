---------------------------- MODULE CounterSpec ----------------------------

CONSTANTS MaxValue == 10

VARIABLES counter

(*--algorithm Counter
variables counter = 0;

while counter < MaxValue do
    await counter < MaxValue;
    counter := counter + 1;
end while;
end algorithm*)

Spec ==
  /\ TYPEOK
  /\ Init
  /\ [][Next]_<<counter>>
  /\ WF_[Next]_<<counter>>

Init == counter = 0

Next ==
  \/ /\ counter < MaxValue
     /\ counter' = counter + 1
  \/ /\ counter >= MaxValue
     /\ counter' = counter

Termination ==
  <>(counter = MaxValue)

(* Fairness to ensure the incrementing step is weakly fair *)
WF_ == WF_[Next]_<<counter>>

THEOREM Spec => []<>(counter = 5)
THEOREM Spec => []<>(/\ counter = 9
                     /\ counter' = 10)

=============================================================================