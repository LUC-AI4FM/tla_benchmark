------------------------------ MODULE OneStepByz ------------------------------
(*****************************************************************************)
(* One-step Byzantine consensus (Algorithm 2, Dobre and Suri, DSN 2006).     *)
(*                                                                           *)
(* Locations of a process:                                                   *)
(*   "V0","V1" : initial value 0 / 1, not yet broadcast                      *)
(*   "S0","S1" : value 0 / 1 broadcast, waiting                              *)
(*   "D0","D1" : decided 0 / 1                                               *)
(*   "U0","U1" : undecided, fell back to own proposal 0 / 1                  *)
(*   "BYZ"     : Byzantine                                                   *)
(*                                                                           *)
(* Messages from correct processes (nSnt0, nSnt1) and from faulty processes  *)
(* (nSnt0F, nSnt1F) are counted separately.  Receiving is abstracted by      *)
(* threshold guards over the sent counters.  The fallback rule fires only    *)
(* once a process has received from every correct process, and neither       *)
(* threshold is reachable.                                                   *)
(*****************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME /\ N \in Nat /\ T \in Nat /\ F \in Nat
       /\ N > 3 * T
       /\ T >= F

Proc == 1 .. N

Locs == {"V0", "V1", "S0", "S1", "D0", "D1", "U0", "U1", "BYZ"}

VARIABLES pc,       \* location of each process
          nSnt0,    \* number of 0-messages sent by correct processes
          nSnt1,    \* number of 1-messages sent by correct processes
          nSnt0F,   \* number of 0-messages sent by faulty processes
          nSnt1F,   \* number of 1-messages sent by faulty processes
          nFaulty   \* number of Byzantine processes

vars == << pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty >>

TypeOK ==
  /\ pc \in [Proc -> Locs]
  /\ nSnt0 \in 0 .. N
  /\ nSnt1 \in 0 .. N
  /\ nSnt0F \in 0 .. N
  /\ nSnt1F \in 0 .. N
  /\ nFaulty \in 0 .. F

Init ==
  /\ pc \in [Proc -> {"V0", "V1"}]
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nSnt0F = 0
  /\ nSnt1F = 0
  /\ nFaulty = 0

Init0 == Init /\ pc = [p \in Proc |-> "V0"]
Init1 == Init /\ pc = [p \in Proc |-> "V1"]

(* All correct processes have broadcast their value. *)
AllCorrectSent == \A q \in Proc : pc[q] \notin {"V0", "V1"}

Total0 == nSnt0 + nSnt0F
Total1 == nSnt1 + nSnt1F

(* ---------------- correct process actions ---------------- *)

Propose(p) ==
  \/ /\ pc[p] = "V0"
     /\ pc' = [pc EXCEPT ![p] = "S0"]
     /\ nSnt0' = nSnt0 + 1
     /\ UNCHANGED << nSnt1, nSnt0F, nSnt1F, nFaulty >>
  \/ /\ pc[p] = "V1"
     /\ pc' = [pc EXCEPT ![p] = "S1"]
     /\ nSnt1' = nSnt1 + 1
     /\ UNCHANGED << nSnt0, nSnt0F, nSnt1F, nFaulty >>

Decide(p) ==
  /\ pc[p] \in {"S0", "S1"}
  /\ \/ /\ Total0 >= N - T
        /\ pc' = [pc EXCEPT ![p] = "D0"]
     \/ /\ Total1 >= N - T
        /\ pc' = [pc EXCEPT ![p] = "D1"]
     \/ /\ AllCorrectSent
        /\ Total0 + Total1 >= N - T
        /\ Total0 < N - T
        /\ Total1 < N - T
        /\ pc' = [pc EXCEPT ![p] = IF pc[p] = "S0" THEN "U0" ELSE "U1"]
  /\ UNCHANGED << nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty >>

Correct(p) == Propose(p) \/ Decide(p)

(* ---------------- Byzantine actions ---------------- *)

BecomeByz(p) ==
  /\ nFaulty < F
  /\ pc[p] \in {"V0", "V1"}
  /\ pc' = [pc EXCEPT ![p] = "BYZ"]
  /\ nFaulty' = nFaulty + 1
  /\ UNCHANGED << nSnt0, nSnt1, nSnt0F, nSnt1F >>

ByzSend ==
  \/ /\ nSnt0F < nFaulty
     /\ nSnt0F' = nSnt0F + 1
     /\ UNCHANGED << pc, nSnt0, nSnt1, nSnt1F, nFaulty >>
  \/ /\ nSnt1F < nFaulty
     /\ nSnt1F' = nSnt1F + 1
     /\ UNCHANGED << pc, nSnt0, nSnt1, nSnt0F, nFaulty >>

Next ==
  \/ \E p \in Proc : Correct(p)
  \/ \E p \in Proc : BecomeByz(p)
  \/ ByzSend
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ \A p \in Proc : WF_vars(Correct(p))

StateConstraint ==
  /\ nSnt0 <= N /\ nSnt1 <= N
  /\ nSnt0F <= N /\ nSnt1F <= N
  /\ nFaulty <= F

(* ---------------- properties ---------------- *)

AllZeroInit == \A p \in Proc : pc[p] = "V0"
AllOneInit  == \A p \in Proc : pc[p] = "V1"

OneStep0_Ltl ==
  AllZeroInit => [](\A p \in Proc : pc[p] \notin {"D1", "U0", "U1"})

OneStep1_Ltl ==
  AllOneInit =>
    /\ <>(\A p \in Proc : pc[p] \in {"D1", "BYZ"})
    /\ [](\A p \in Proc : pc[p] \notin {"D0", "U0", "U1"})

AllDecideOne ==
  AllOneInit => <>[](\A p \in Proc : pc[p] \in {"D1", "BYZ"})

=============================================================================