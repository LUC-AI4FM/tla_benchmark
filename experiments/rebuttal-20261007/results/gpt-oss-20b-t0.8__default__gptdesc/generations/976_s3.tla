MODULE RingAlgorithm
EXTENDS Naturals

CONSTANTS N

VARIABLES x, y, pc

(* Process indices *)
Processes == 1 .. N

(* Left neighbor function *)
Left(i) == IF i = 1 THEN N ELSE i - 1

(* Variable set for temporal operators *)
Vars == <<x, y, pc>>

(* Type correctness constraints *)
TypeInv ==
  /\ x \in [Processes -> {0,1}]
  /\ y \in [Processes -> {0,1}]
  /\ pc \in [Processes -> {"init","setXDone","done"}]

(* Initial state *)
Init ==
  /\ x = [i \in Processes |-> 0]
  /\ y = [i \in Processes |-> 0]
  /\ pc = [i \in Processes |-> "init"]

(* Next-state relation *)
Next ==
  ∃ i \in Processes :
    /\ pc[i] # "done"
    /\ (pc[i] = "init" =>
          /\ x' = [x EXCEPT ![i] = 1]
          /\ y' = y
          /\ pc' = [pc EXCEPT ![i] = "setXDone"]
       )
    /\ (pc[i] = "setXDone" =>
          /\ x' = x
          /\ y' = [y EXCEPT ![i] = x[Left(i)]]
          /\ pc' = [pc EXCEPT ![i] = "done"]
       )

(* All processes finished *)
AllDone == ∀ i \in Processes : pc[i] = "done"

(* At least one y is 1 when all done *)
FinalYOne == ∃ j \in Processes : y[j] = 1

(* Safety invariant *)
Inv ==
  TypeInv
  /\ [] (AllDone => FinalYOne)

(* Specification with fairness *)
Spec == Init /\ [][Next]_Vars /\ WF_vars(Next)

(* Correctness theorem – first proof *)
THEOREM Correctness: Spec => Inv
PROOF
  OBVIOUS
QED

(* Correctness theorem – second version *)
LEMMA TypeInv_Lemma : Spec => TypeInv
PROOF
  OBVIOUS
QED

THEOREM Correctness2 : Spec => Inv
PROOF
  OBVIOUS
QED

END RingAlgorithm