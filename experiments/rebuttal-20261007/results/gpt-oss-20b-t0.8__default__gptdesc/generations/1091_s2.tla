MODULE PCR
EXTENDS Naturals

CONSTANTS HEATING, COOLING, ANNEALING, EXTENDING

VARIABLES Temp, Primers, Templates, Hybrids, DNA, InitSum

(* ------------------------------------------------------------------ *)
(* Types and invariants *)

PhaseSet == {HEATING, COOLING, ANNEALING, EXTENDING}

TypeInvariant ==
  /\ Temp \in PhaseSet
  /\ Primers \in Nat
  /\ Templates \in Nat
  /\ Hybrids \in Nat
  /\ DNA \in Nat

Min(a,b) == IF a <= b THEN a ELSE b

CountInvariant ==
  Primers + Templates + Hybrids + DNA = InitSum

Safety == TypeInvariant /\ CountInvariant

(* ------------------------------------------------------------------ *)
(* Initial state *)

Init ==
  /\ Temp = HEATING
  /\ Primers = 5
  /\ Templates = 3
  /\ Hybrids = 0
  /\ DNA = 0
  /\ InitSum = Primers + Templates + Hybrids + DNA

(* ------------------------------------------------------------------ *)
(* Actions *)

Heating ==
  /\ Temp' = COOLING
  /\ UNCHANGED <<Primers, Templates, Hybrids, DNA, InitSum>>

Cooling ==
  /\ Temp' = ANNEALING
  /\ UNCHANGED <<Primers, Templates, Hybrids, DNA, InitSum>>

Annealing ==
  LET n == CHOOSE i \in 0..Min(Primers, Templates) IN
    /\ Temp' = EXTENDING
    /\ Primers' = Primers - n
    /\ Templates' = Templates - n
    /\ Hybrids' = Hybrids + n
    /\ DNA' = DNA
    /\ InitSum' = InitSum

Extension ==
  LET m == CHOOSE j \in 0..Hybrids IN
    /\ Temp' = HEATING
    /\ Primers' = Primers
    /\ Templates' = Templates
    /\ Hybrids' = Hybrids - m
    /\ DNA' = DNA + m
    /\ InitSum' = InitSum

Next == Heating \/ Cooling \/ Annealing \/ Extension

(* ------------------------------------------------------------------ *)
(* Specification *)

Spec ==
  Init
  /\ [][Next]_(<<Temp, Primers, Templates, Hybrids, DNA, InitSum>>)
  /\ Safety

(* ------------------------------------------------------------------ *)
(* Liveness property *)

Liveness ==
  <> (Primers = 0)