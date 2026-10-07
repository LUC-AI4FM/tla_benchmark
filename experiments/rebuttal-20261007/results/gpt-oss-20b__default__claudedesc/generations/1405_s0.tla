------------------------------ MODULE Inner725f ------------------------------
EXTENDS Sequences

VARIABLES res, myseq

RemoveEqual(seq, val) ==
  IF Len(seq)=0 THEN <<>>
  ELSE
    LET h = Head(seq)
        t = Tail(seq)
    IN IF h = val THEN RemoveEqual(t, val)
       ELSE <<h>> ^ RemoveEqual(t, val)

Init == 
  /\ res = 0
  /\ myseq = <<1,2,3>>

Step ==
  /\ res = 0
  /\ res' = 1
  /\ myseq' = RemoveEqual(myseq, 1)
-----------------------------------------------------------------------

------------------------------ MODULE Outer ------------------------------
EXTENDS Sequences

VARIABLES outerRes, outerSeq

(* Instantiate the inner module with variable renaming *)
INSTANCE Inner725f WITH res = outerRes, myseq = outerSeq

Init == 
  /\ outerRes = 0
  /\ outerSeq = <<1,2,3>>

Next == Step \/ UNCHANGED <<outerRes, outerSeq>>

Spec == Init /\ [][Next]_<<outerRes, outerSeq>> /\ WF_vars(Step)

SpecRunsToEnd == <> (outerRes = 1 /\ [] (outerRes = 1))
-----------------------------------------------------------------------