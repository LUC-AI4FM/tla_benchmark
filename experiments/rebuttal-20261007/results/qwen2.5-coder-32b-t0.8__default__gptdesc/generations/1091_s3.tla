------------------------------- MODULE PcrCycle -------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS MaxPrimers, MaxTemplates

VARIABLES Temp, Primers, Dna, Templates, Hybrids

(* --algorithm pcr_cycle
variables 
  Temp \in {HEATING, COOLING, ANNEALING, EXTENSION},
  Primers \in 0..MaxPrimers,
  Dna \in 0..MaxTemplates,
  Templates \in 0..MaxTemplates,
  Hybrids \in 0..MaxTemplates
begin
  Temp := HEATING;
  Primers := MaxPrimers;
  Dna := 0;
  Templates := MaxTemplates;
  Hybrids := 0;
  while TRUE do
    if Temp = HEATING then
      Temp := COOLING
    else if Temp = COOLING then
      Temp := ANNEALING
    else if Temp = ANNEALING then
      with n \in 0..min(Primers, Templates) do
        Primers := Primers - n;
        Templates := Templates - n;
        Hybrids := Hybrids + n;
      endwith;
      Temp := EXTENSION
    else if Temp = EXTENSION then
      Dna := Dna + Hybrids;
      Hybrids := 0;
      Temp := HEATING
    end if;
  od;
end algorithm *)

Init == /\ Temp \in {HEATING, COOLING, ANNEALING, EXTENSION}
        /\ Primers \in 0..MaxPrimers
        /\ Dna = 0
        /\ Templates \in 0..MaxTemplates
        /\ Hybrids = 0

Next ==
    \/ /\ Temp = HEATING
       /\ Temp' = COOLING
       /\ UNCHANGED <<Primers, Dna, Templates, Hybrids>>
    \/ /\ Temp = COOLING
       /\ Temp' = ANNEALING
       /\ UNCHANGED <<Primers, Dna, Templates, Hybrids>>
    \/ /\ Temp = ANNEALING
       /\ \E n \in 0..min(Primers, Templates) :
            Primers' = Primers - n
            /\ Templates' = Templates - n
            /\ Hybrids' = Hybrids + n
            /\ Temp' = EXTENSION
            /\ UNCHANGED <<Dna>>
    \/ /\ Temp = EXTENSION
       /\ Dna' = Dna + Hybrids
       /\ Hybrids' = 0
       /\ Temp' = HEATING
       /\ UNCHANGED <<Primers, Templates>>

Spec == Init /\ [][Next]_<<Temp, Primers, Dna, Templates, Hybrids>>

Inv1 == \/ Temp = HEATING \/ Temp = COOLING \/ Temp = ANNEALING \/ Temp = EXTENSION
Inv2 == Primers \in 0..MaxPrimers
Inv3 == Dna \in 0..MaxTemplates
Inv4 == Templates \in 0..MaxTemplates
Inv5 == Hybrids \in 0..MaxTemplates
Inv6 == Primers + Dna + Templates + Hybrids = MaxPrimers + MaxTemplates

Safety == Inv1 /\ Inv2 /\ Inv3 /\ Inv4 /\ Inv5 /\ Inv6

Liveness == <>F(Primers' = 0)

Fairness ==
    WF_next(Temp, HEATING)
    /\ WF_next(Temp, COOLING)
    /\ WF_next(Temp, ANNEALING)
    /\ WF_next(Temp, EXTENSION)

=============================================================================