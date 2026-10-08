MODULE OneVarSystem
EXTENDS Naturals, Sequences, TLC

VARIABLE x

Init == x = 0

Next ==
  \/ (x = 0 /\ x' \in {1,2})
  \/ (x # 0 /\ x' = 0)

StabilizeP    == <> [] (x = 0)
RepeatedZeroP == [] <> (x = 0)
NotRepeatedZeroP == ~ RepeatedZeroP

Spec == Init
        /\ [][Next]_x
        /\ WF_x(Next)
        /\ StabilizeP
        /\ RepeatedZeroP
        /\ NotRepeatedZeroP

STATE == [x : Nat]

State0 == [x |-> 0]
State1 == [x |-> 1]
State2 == [x |-> 0]

PostCondition ==
  \E seq \in Seq(STATE) :
    /\ Len(seq) = 3
    /\ seq[1] = State0
    /\ seq[2] = State1
    /\ seq[3] = State2

===============================================================================