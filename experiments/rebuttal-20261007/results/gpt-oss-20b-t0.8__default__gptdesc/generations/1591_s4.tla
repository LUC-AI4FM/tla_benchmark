------------------------------ MODULE EvenOdd ------------------------------
EXTENDS Naturals, TLC

CONSTANT N \* The input natural number

VARIABLES pc, n, result

(* --------------------------------------------------------------------------- *)
(* Type constraints and invariants                                           *)
(* --------------------------------------------------------------------------- *)

TypeInvariant == 
  /\ pc ∈ {"Even", "Odd", "Done"}
  /\ n ∈ Int
  /\ n >= 0
  /\ result ∈ BOOLEAN ∪ {⊥}

SafetyInv == (pc = "Done") => (result ∈ {TRUE, FALSE})

(* --------------------------------------------------------------------------- *)
(* Initial state                                                              *)
(* --------------------------------------------------------------------------- *)

Init == 
  /\ pc = "Even"
  /\ n = N
  /\ result = ⊥

(* --------------------------------------------------------------------------- *)
(* Next-state relation for each control location                            *)
(* --------------------------------------------------------------------------- *)

EvenStep == 
  /\ pc = "Even"
  /\ n > 0
  /\ UNCHANGED result
  /\ pc' = "Odd"
  /\ n' = n - 1

EvenTerm == 
  /\ pc = "Even"
  /\ n = 0
  /\ pc' = "Done"
  /\ result' = TRUE
  /\ UNCHANGED n

OddStep == 
  /\ pc = "Odd"
  /\ n > 0
  /\ UNCHANGED result
  /\ pc' = "Even"
  /\ n' = n - 1

OddTerm == 
  /\ pc = "Odd"
  /\ n = 0
  /\ pc' = "Done"
  /\ result' = FALSE
  /\ UNCHANGED n

DoneStutter == 
  /\ pc = "Done"
  /\ UNCHANGED <<pc, n, result>>

Next == EvenStep \/ OddStep \/ EvenTerm \/ OddTerm \/ DoneStutter

(* --------------------------------------------------------------------------- *)
(* Temporal specification with weak fairness and eventual termination      *)
(* --------------------------------------------------------------------------- *)

Spec == 
  Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
  /\ TypeInvariant
  /\ SafetyInv
  /\ <> (pc = "Done")

=============================================================================