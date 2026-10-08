MODULE RegularRegisterProtocol
EXTENDS Naturals

CONSTANT N

VARIABLES regVal, pending, local, pc

(* Helper function for left neighbor *)
Left(i) == IF i = 1 THEN N ELSE i - 1

BeginWrite(i) ==
  /\ pc[i] = "Begin"
  /\ pending[i] = "None"
  /\ pending[i]' = 1
  /\ pc[i]' = "Complete"

CompleteWrite(i) ==
  /\ pc[i] = "Complete"
  /\ pending[i] = 1
  /\ regVal[i]' = 1
  /\ pending[i]' = "None"
  /\ pc[i]' = "Read"

ReadNeighbor(i) ==
  LET j == Left(i)
      possibleValues == IF pending[j] = "None" THEN {regVal[j]} ELSE {regVal[j], pending[j]}
  IN
    /\ pc[i] = "Read"
    /\ local[i]' ∈ possibleValues
    /\ pc[i]' = "Done"

Next ==
  ∨ i \in 1..N : BeginWrite(i) \/ CompleteWrite(i) \/ ReadNeighbor(i)

Init ==
  /\ regVal   = [i \in 1..N |-> 0]
  /\ pending  = [i \in 1..N |-> "None"]
  /\ local    = [i \in 1..N |-> 0]
  /\ pc       = [i \in 1..N |-> "Begin"]

TypeInv ==
  /\ regVal   ∈ [1..N -> {0,1}]
  /\ pending  ∈ [1..N -> {"None", 0, 1}]
  /\ local    ∈ [1..N -> {0,1}]
  /\ pc       ∈ [1..N -> {"Begin","Complete","Read","Done"}]
  /\ ∀i \in 1..N : pending[i] = "None" \/ pending[i] = 1

Safety ==
  [] ( (∀i \in 1..N : pc[i] = "Done") => (∃i \in 1..N : local[i] = 1) )

Progress ==
  <> ( ∀i \in 1..N : pc[i] = "Done" )

vars == <<regVal, pending, local, pc>>

Spec == Init /\ [][Next]_vars /\ Safety /\ Progress

END MODULE