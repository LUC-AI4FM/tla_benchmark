---------------------------- MODULE Spec ----------------------------
EXTENDS Integers

VARIABLE counter
VARIABLE witnesses

Init == (counter = 0) /\
        (witnesses = <<>>)

Next == (counter' = (counter + 1) % 3) /\
        (witnesses' = IF counter = 2 THEN <<2>> ++ witnesses
                  ELSE IF counter = 1 THEN <<1>> ++ witnesses
                  ELSE IF counter' = 0 THEN <<0>> ++ witnesses
                  ELSE witnesses)

AtTwo == (counter = 2)
AtOne == (counter = 1)
WrapAround == (counter = 2) /\ (counter' = 0)

Spec == Init /\ [][Next]_<<counter, witnesses>>

THEOREM Spec => <>(AtTwo /\ AtOne /\ WrapAround)
====================================================================