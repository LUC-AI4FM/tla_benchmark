------------------------------ MODULE BridgePetersonLock ------------------------------

EXTENDS Naturals, TLC

CONSTANTS Proc, InitTurn

ASSUME Proc = {0, 1} /\ InitTurn \in Proc

(*
  Two-process augmented lock with:
  - pc: program counter for each process
  - s: stuttering counter to expand a single entry step into three sub-steps
  - hTurn: history variable tracking the last assignment to Peterson's 'turn'
*)

VARIABLES pc, s, hTurn

ProcSet == Proc
Other(p) == CHOOSE q \in ProcSet: q # p

Labels == {"N", "E", "C", "X"}

TypeInv ==
  /\ pc \in [ProcSet -> Labels]
  /\ s \in [ProcSet -> 0..3]
  /\ hTurn \in ProcSet

\* Stuttering discipline: in E iff s in 1..3; otherwise s = 0
StutterInv ==
  \A p \in ProcSet:
    (pc[p] = "E") <=> (s[p] \in 1..3)

\* Derived "Peterson view"
PetLabels == {"L0", "L1", "L2", "L3", "L4", "L5"}

PetPc(p) ==
  IF pc[p] = "N" THEN "L0"
  ELSE IF pc[p] = "E" /\ s[p] = 1 THEN "L1"
  ELSE IF pc[p] = "E" /\ s[p] = 2 THEN "L2"
  ELSE IF pc[p] = "E" /\ s[p] = 3 THEN "L3"
  ELSE IF pc[p] = "C" THEN "L4"
  ELSE (* pc[p] = "X" *)
    "L5"

\* Derived Peterson 'want' flag
Want(p) ==
  IF pc[p] = "E" THEN s[p] \in 1..3
  ELSE pc[p] = "C"

\* Derived Peterson 'turn' variable from history
Turn == hTurn

\* Type correctness of the derived Peterson view
PetersonViewType ==
  /\ \A p \in ProcSet: PetPc(p) \in PetLabels
  /\ \A p \in ProcSet: Want(p) \in BOOLEAN
  /\ Turn \in ProcSet

\* Mutual exclusion
Mutex ==
  \A p, q \in ProcSet: p # q => ~ (pc[p] = "C" /\ pc[q] = "C")

\* Turn-ownership relation with program counters and stuttering phase:
\* If p has assigned (or is past assigning) turn (s in {2,3}) and the other
\* is not also in/after assigning, then hTurn must equal Other(p).
TurnOwnershipInv ==
  \A p \in ProcSet:
    (pc[p] = "E" /\ s[p] \in {2, 3}
      /\ ~ (pc[Other(p)] = "E" /\ s[Other(p)] \in {2, 3}))
    => hTurn = Other(p)

TypeOK == TypeInv /\ StutterInv /\ PetersonViewType

Init ==
  /\ pc = [p \in ProcSet |-> "N"]
  /\ s = [p \in ProcSet |-> 0]
  /\ hTurn = InitTurn

\* Guard to enter CS that mirrors Peterson's await:
\*   not Want(other) or Turn = p
\* Also requires no one is already in CS.
NoOtherInC(p) == \A q \in ProcSet \ {p}: pc[q] # "C"

CanEnter(p) ==
  /\ NoOtherInC(p)
  /\ (~ Want(Other(p)) \/ Turn = p)

N2E(p) ==
  /\ pc[p] = "N"
  /\ pc' = [pc EXCEPT ![p] = "E"]
  /\ s' = [s EXCEPT ![p] = 1]
  /\ UNCHANGED hTurn

EStutter1(p) ==
  /\ pc[p] = "E" /\ s[p] = 1
  /\ s' = [s EXCEPT ![p] = 2]
  /\ UNCHANGED <<pc, hTurn>>

EStutter2(p) ==
  /\ pc[p] = "E" /\ s[p] = 2
  /\ s' = [s EXCEPT ![p] = 3]
  /\ hTurn' = Other(p)
  /\ UNCHANGED pc

EEnter(p) ==
  /\ pc[p] = "E" /\ s[p] = 3
  /\ CanEnter(p)
  /\ pc' = [pc EXCEPT ![p] = "C"]
  /\ s' = [s EXCEPT ![p] = 0]
  /\ UNCHANGED hTurn

C2X(p) ==
  /\ pc[p] = "C"
  /\ pc' = [pc EXCEPT ![p] = "X"]
  /\ UNCHANGED <<s, hTurn>>

X2N(p) ==
  /\ pc[p] = "X"
  /\ pc' = [pc EXCEPT ![p] = "N"]
  /\ UNCHANGED <<s, hTurn>>

Step(p) == N2E(p) \/ EStutter1(p) \/ EStutter2(p) \/ EEnter(p) \/ C2X(p) \/ X2N(p)

Next == \E p \in ProcSet: Step(p)

Spec == Init /\ [][Next]_<<pc, s, hTurn>>

Inv == TypeOK /\ Mutex /\ TurnOwnershipInv

THEOREM Spec => []Inv

(***************************************************************************)
(*                       Base (abstract) lock spec                         *)
(***************************************************************************)

BaseInit == \A p \in ProcSet: pc[p] = "N"

BaseNoOtherInC(p) == \A q \in ProcSet \ {p}: pc[q] # "C"

BaseN2E(p) ==
  /\ pc[p] = "N"
  /\ pc' = [pc EXCEPT ![p] = "E"]

BaseE2C(p) ==
  /\ pc[p] = "E"
  /\ BaseNoOtherInC(p)
  /\ pc' = [pc EXCEPT ![p] = "C"]

BaseC2X(p) ==
  /\ pc[p] = "C"
  /\ pc' = [pc EXCEPT ![p] = "X"]

BaseX2N(p) ==
  /\ pc[p] = "X"
  /\ pc' = [pc EXCEPT ![p] = "N"]

BaseNext == \E p \in ProcSet: BaseN2E(p) \/ BaseE2C(p) \/ BaseC2X(p) \/ BaseX2N(p)

BaseSpec == BaseInit /\ [][BaseNext]_pc

THEOREM Spec => BaseSpec

(***************************************************************************)
(*        Peterson spec under the refinement mapping (derived view)        *)
(***************************************************************************)

PetInitRM ==
  /\ \A p \in ProcSet: PetPc(p) = "L0"
  /\ \A p \in ProcSet: ~ Want(p)
  /\ Turn \in ProcSet

\* Convenience shorthands for "unchanged" in the derived view
UnchAllPet ==
  /\ \A r \in ProcSet: PetPc'(r) = PetPc(r)
  /\ \A r \in ProcSet: Want'(r) = Want(r)
  /\ Turn' = Turn

UnchOtherPet(p) ==
  /\ PetPc'(Other(p)) = PetPc(Other(p))
  /\ Want'(Other(p)) = Want(Other(p))

UnchWantAll ==
  \A r \in ProcSet: Want'(r) = Want(r)

UnchPetersonExceptTurn ==
  /\ UnchWantAll
  /\ \A r \in ProcSet: PetPc'(r) = PetPc(r)

PetStep(p) ==
  \/ /\ PetPc(p) = "L0" /\ PetPc'(p) = "L1"
     /\ Want'(p) = TRUE
     /\ Turn' = Turn
     /\ UnchOtherPet(p)
  \/ /\ PetPc(p) = "L1" /\ PetPc'(p) = "L2"
     /\ Want'(p) = TRUE
     /\ Turn' = Turn
     /\ UnchOtherPet(p)
  \/ /\ PetPc(p) = "L2" /\ PetPc'(p) = "L3"
     /\ UnchOtherPet(p)
     /\ UnchWantAll
     /\ Turn' = Turn
  \/ /\ PetPc(p) = "L3"
     /\ (~ Want(Other(p)) \/ Turn = p)
     /\ PetPc'(p) = "L4"
     /\ UnchOtherPet(p)
     /\ UnchWantAll
     /\ Turn' = Turn
  \/ /\ PetPc(p) = "L4" /\ PetPc'(p) = "L5"
     /\ UnchOtherPet(p)
     /\ UnchWantAll
     /\ Turn' = Turn
  \/ /\ PetPc(p) = "L5" /\ PetPc'(p) = "L0"
     /\ Want'(p) = FALSE
     /\ Turn' = Turn
     /\ UnchOtherPet(p)

PetNextRM == \E p \in ProcSet: PetStep(p)

PetSpecRM == PetInitRM /\ [] (PetNextRM \/ UnchAllPet)

THEOREM Spec => PetSpecRM

=============================================================================