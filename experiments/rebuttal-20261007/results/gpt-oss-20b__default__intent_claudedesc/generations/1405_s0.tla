------------------------------ MODULE Inner ------------------------------
EXTENDS Sequences

VARIABLES res, seq

Init == /\ res = 0
      /\ seq = <<>>

Step == /\ res = 0
       /\ LET newRes == 1 IN
          /\ res' = newRes
          /\ seq' = Filter(seq, \x \in seq : x != newRes)

Next == Step

SpecInner == Init /\ [][Next]_<<res, seq>>
END MODULE

------------------------------ MODULE Outer ------------------------------
EXTENDS Sequences

VARIABLES result, sequence

INSTANCE Inner(res -> result, seq -> sequence)

InitOuter == /\ result = 0
            /\ sequence = <<1,2,3>>

NextOuter == Inner.Step \/ (¬Enabled(Inner.Step) /\ UNCHANGED <<result, sequence>>)

Termination == <> (¬Enabled(Inner.Step))

Spec == InitOuter /\ [][NextOuter]_<<result, sequence>> /\ Fairness(Inner.Step) /\ Termination
END MODULE