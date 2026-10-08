----------------------------- MODULE PCR -----------------------------

EXTENDS Naturals, Integers

CONSTANTS
  LFull,       \* full-length strand nucleotide units (positive integer)
  LPrimer,     \* primer length in nucleotide units (positive integer, <= LFull)
  DS0, SS0, H0, P0, N0,  \* initial counts
  StartPhase   \* initial temperature phase

Phases == {"Denaturation", "Annealing", "Extension"}

ASSUME /\ LFull \in Nat /\ LFull > 0
       /\ LPrimer \in Nat /\ LPrimer > 0 /\ LPrimer <= LFull
       /\ DS0 \in Nat /\ SS0 \in Nat /\ H0 \in Nat /\ P0 \in Nat /\ N0 \in Nat
       /\ StartPhase \in Phases

VARIABLES phase, DS, SS, H, P, N

vars == << phase, DS, SS, H, P, N >>

\* Helper definitions
Min(a, b) == IF a <= b THEN a ELSE b
NeedN == LFull - LPrimer

\* System mass accounting (nucleotide units):
\* - each full-length strand contributes LFull
\* - each primer contributes LPrimer
\* - DS = 2 full-length strands
\* - SS = 1 full-length strand
\* - H = 1 full-length template + 1 primer
\* - N = free nucleotide units pool
Mass == 2*DS*LFull + SS*LFull + H*(LFull + LPrimer) + P*LPrimer + N

Total0 == 2*DS0*LFull + SS0*LFull + H0*(LFull + LPrimer) + P0*LPrimer + N0

TypeOK ==
  /\ phase \in Phases
  /\ DS \in Nat /\ SS \in Nat /\ H \in Nat /\ P \in Nat /\ N \in Nat

Init ==
  /\ TypeOK
  /\ phase = StartPhase
  /\ DS = DS0 /\ SS = SS0 /\ H = H0 /\ P = P0 /\ N = N0

\* Denaturation: melt double strands and/or break hybrids,
\* releasing single strands and any bound primers
DenatureAct ==
  /\ phase = "Denaturation"
  /\ \E x \in 0..DS, y \in 0..H:
       /\ DS' = DS - x
       /\ SS' = SS + 2*x + y
       /\ H'  = H - y
       /\ P'  = P + y
       /\ N'  = N
       /\ phase' = phase

\* Annealing: consume primers and single-stranded templates to form hybrids
AnnealAct ==
  /\ phase = "Annealing"
  /\ \E d \in 1..Min(P, SS):
       /\ P' = P - d
       /\ SS' = SS - d
       /\ H'  = H + d
       /\ DS' = DS
       /\ N'  = N
       /\ phase' = phase

\* Extension: extend hybrids to new double strands, consuming nucleotides
ExtendAct ==
  /\ phase = "Extension"
  /\ \E e \in 1..H:
       /\ e*NeedN <= N
       /\ DS' = DS + e
       /\ H'  = H - e
       /\ N'  = N - e*NeedN
       /\ SS' = SS
       /\ P'  = P
       /\ phase' = phase

\* Phase transitions (thermocycling)
DtoA ==
  /\ phase = "Denaturation"
  /\ phase' = "Annealing"
  /\ UNCHANGED << DS, SS, H, P, N >>

AtoE ==
  /\ phase = "Annealing"
  /\ phase' = "Extension"
  /\ UNCHANGED << DS, SS, H, P, N >>

EtoD ==
  /\ phase = "Extension"
  /\ phase' = "Denaturation"
  /\ UNCHANGED << DS, SS, H, P, N >>

Next ==
  DenatureAct \/ AnnealAct \/ ExtendAct \/ DtoA \/ AtoE \/ EtoD

\* Fairness: enforce infinite cycling and eventual reactions when enabled infinitely often
Fairness ==
  /\ SF_vars(DtoA) /\ SF_vars(AtoE) /\ SF_vars(EtoD)
  /\ SF_vars(AnnealAct)
  /\ SF_vars(ExtendAct)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety properties
ConservationInvariant == Mass = Total0
Nonnegativity == TypeOK
Safety == []ConservationInvariant /\ []Nonnegativity

\* Liveness of cycling: each phase is visited infinitely often
CycleLiveness ==
  /\ []<>(phase = "Denaturation")
  /\ []<>(phase = "Annealing")
  /\ []<>(phase = "Extension")

\* Under sufficient initial resources, additional double-stranded product eventually appears
AmplifiableInit ==
  /\ P0 > 0
  /\ N0 >= NeedN
  /\ (SS0 + 2*DS0 + H0) > 0

AmplifyEventually ==
  AmplifiableInit => <> (DS > DS0)

\* Resource depletion consequence: without primers and hybrids, extension is impossible
NoExtendWithoutPrimers ==
  [] ((P = 0 /\ H = 0) => ~ENABLED ExtendAct)

=====================================================================