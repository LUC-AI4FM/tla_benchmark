------------------------------ MODULE Inner ------------------------------
EXTENDS Naturals, Sequences

VARIABLE result, seq

Init == 
  /\ result = 0
  /\ seq = <<1,2,3>>

Next ==
  /\ result = 0
  /\ result' = 1
  /\ seq' = SubSeq(seq,
          { i \in 1..Len(seq) : ~(seq[i] = result') })

------------------------------ MODULE Outer ------------------------------
EXTENDS Naturals, Sequences

VARIABLES r, s

(* Instantiate Inner with renamed variables *)
INSTANCE Inner AS Inn WITH result = r, seq = s

Init == 
  /\ r = 0
  /\ s = <<1,2,3>>

Stutter == 
  /\ r' = r
  /\ s' = s

Next == 
  \/ Inn.Next
  \/ Stutter

Spec == Init /\ [][Next]_(r,s) /\ WF/Inn.Next

ASSERT ◇◻~(Inn.Next)