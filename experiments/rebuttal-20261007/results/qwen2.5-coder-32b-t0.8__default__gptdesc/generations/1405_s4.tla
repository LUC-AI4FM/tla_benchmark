---- MODULE OuterModule ----

EXTENDS TLC, Integers, Sequences

CONSTANTS InnerResult, InnerSeq

VARIABLES result, seq

InnerSpec ==
  VARIABLES innerResult, innerSeq
  Init == /\ innerResult = 0 
          /\ innerSeq = <<>>
  Next == \/ /\ innerResult = 0 
              /\ innerSeq' = SelectSeq(innerSeq, LAMBDA x: x # 1)
              /\ innerResult' = 1
          \/ /\ UNCHANGED innerResult
              /\ UNCHANGED innerSeq
  Spec == Init /\ [][Next]_<<innerResult, innerSeq>>

INSTANCE InnerSpec WITH 
  innerResult <- result,
  innerSeq <- seq

Init == /\ result = 0 
        /\ seq = <<>>

Next == \/ InnerSpec!Next
        \/ /\ UNCHANGED result
           /\ UNCHANGED seq

Spec == Init /\ [][Next]_<<result, seq>> /\ WF_next(Next)

WF_next(action) == <>(\E state \in StateSpace : action)

StateSpace == { <<r, s>>: r = 0 \/ r = 1 /\ s \in Seq(Nat) }

FinallyDisabled ==
  <>[] (/\ result = 1
        /\ ~InnerSpec!Next)

====