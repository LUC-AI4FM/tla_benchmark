------------------------------- MODULE OnePlaceChannel -------------------------------

EXTENDS Naturals

CONSTANT Val

VARIABLES ch

vars == << ch >>

TypeInv ==
  ch \in [ val: Val, rdy: {0, 1}, ack: {0, 1} ]

Init ==
  /\ TypeInv
  /\ ch.rdy = ch.ack

Send ==
  /\ ch.rdy = ch.ack
  /\ \E v \in Val:
        ch' = [ ch EXCEPT
                  !.val = v,
                  !.rdy = 1 - @,
                  !.ack = @ ]

Recv ==
  /\ ch.rdy # ch.ack
  /\ ch' = [ ch EXCEPT
               !.ack = 1 - @,
               !.rdy = @,
               !.val = @ ]

Next ==
  Send \/ Recv

Spec ==
  Init /\ [][Next]_vars

Safety ==
  []TypeInv

THEOREM Spec => Safety

=====================================================================================