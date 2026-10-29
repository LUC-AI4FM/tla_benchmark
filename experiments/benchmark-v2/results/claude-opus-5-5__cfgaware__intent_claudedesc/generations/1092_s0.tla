------------------------------- MODULE PCR -------------------------------
EXTENDS Naturals

CONSTANTS DNA,      \* initial number of (full-length) double-stranded molecules
          PRIMER    \* initial supply of free primers

ASSUME DNA \in Nat /\ PRIMER \in Nat

VARIABLES
    primer,                  \* free primers in solution
    tFull, tInter, tShort,   \* single-stranded templates by length
    hFull, hInter, hShort,   \* hybrids: template + annealed primer, by template length
    dOrig,                   \* original full-length double strands (full/full)
    dLong,                   \* full template + intermediate new strand
    dMid,                    \* intermediate template + short new strand
    dShort,                  \* exact-length PCR product (short/short)
    stage,                   \* thermal stage
    cycle                    \* number of completed (productive) cycles

vars == << primer, tFull, tInter, tShort, hFull, hInter, hShort,
           dOrig, dLong, dMid, dShort, stage, cycle >>

Stages == {"init", "denatured", "cooled", "annealed", "extended"}

Min(a, b) == IF a < b THEN a ELSE b

-----------------------------------------------------------------------------
(* Aggregate (abstract) views of the molecular inventory                   *)

templateA == tFull + tInter + tShort
hybridA   == hFull + hInter + hShort
dnaA      == dOrig + dLong + dMid + dShort

-----------------------------------------------------------------------------
TypeOK ==
    /\ primer \in Nat
    /\ tFull \in Nat /\ tInter \in Nat /\ tShort \in Nat
    /\ hFull \in Nat /\ hInter \in Nat /\ hShort \in Nat
    /\ dOrig \in Nat /\ dLong \in Nat /\ dMid \in Nat /\ dShort \in Nat
    /\ stage \in Stages
    /\ cycle \in Nat

Init ==
    /\ primer = PRIMER
    /\ tFull = 0 /\ tInter = 0 /\ tShort = 0
    /\ hFull = 0 /\ hInter = 0 /\ hShort = 0
    /\ dOrig = DNA /\ dLong = 0 /\ dMid = 0 /\ dShort = 0
    /\ stage = "init"
    /\ cycle = 0

(* Extreme heat: every double strand and hybrid separates.                 *)
Denature ==
    /\ stage \in {"init", "extended"}
    /\ tFull'  = tFull  + hFull  + 2 * dOrig + dLong
    /\ tInter' = tInter + hInter + dLong + dMid
    /\ tShort' = tShort + hShort + dMid + 2 * dShort
    /\ primer' = primer + hFull + hInter + hShort
    /\ hFull' = 0 /\ hInter' = 0 /\ hShort' = 0
    /\ dOrig' = 0 /\ dLong' = 0 /\ dMid' = 0 /\ dShort' = 0
    /\ stage' = "denatured"
    /\ UNCHANGED cycle

(* Cooling in preparation for annealing.                                   *)
Cool ==
    /\ stage = "denatured"
    /\ stage' = "cooled"
    /\ UNCHANGED << primer, tFull, tInter, tShort, hFull, hInter, hShort,
                    dOrig, dLong, dMid, dShort, cycle >>

(* Warm: primers bind nondeterministically to available templates.         *)
(* At least one primer binds whenever binding is possible.                 *)
Anneal ==
    /\ stage = "cooled"
    /\ \E kF \in 0..Min(primer, tFull) :
       \E kI \in 0..Min(primer, tInter) :
       \E kS \in 0..Min(primer, tShort) :
         /\ kF + kI + kS <= primer
         /\ (primer > 0 /\ templateA > 0) => (kF + kI + kS >= 1)
         /\ tFull'  = tFull  - kF
         /\ tInter' = tInter - kI
         /\ tShort' = tShort - kS
         /\ hFull'  = hFull  + kF
         /\ hInter' = hInter + kI
         /\ hShort' = hShort + kS
         /\ primer' = primer - (kF + kI + kS)
    /\ stage' = "annealed"
    /\ UNCHANGED << dOrig, dLong, dMid, dShort, cycle >>

(* Moderate heat: hybrids are extended into double strands.                *)
Extend ==
    /\ stage = "annealed"
    /\ dLong'  = dLong  + hFull
    /\ dMid'   = dMid   + hInter
    /\ dShort' = dShort + hShort
    /\ hFull' = 0 /\ hInter' = 0 /\ hShort' = 0
    /\ stage' = "extended"
    /\ cycle' = IF hybridA > 0 THEN cycle + 1 ELSE cycle
    /\ UNCHANGED << primer, tFull, tInter, tShort, dOrig >>

Next == Denature \/ Cool \/ Anneal \/ Extend

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties                                                              *)

thirdCycleProduct == (dShort > 0) => (cycle >= 3)

primerDepleted == <>(primer = 0)

StageProgress == []<>(stage = "extended")

-----------------------------------------------------------------------------
(* Abstract specification: aggregate template, hybrid and dna counts.      *)

absVars == << primer, templateA, hybridA, dnaA, stage, cycle >>

AInit ==
    /\ primer = PRIMER
    /\ templateA = 0
    /\ hybridA = 0
    /\ dnaA = DNA
    /\ stage = "init"
    /\ cycle = 0

ADenature ==
    /\ stage \in {"init", "extended"}
    /\ templateA' = templateA + hybridA + 2 * dnaA
    /\ primer' = primer + hybridA
    /\ hybridA' = 0
    /\ dnaA' = 0
    /\ stage' = "denatured"
    /\ cycle' = cycle

ACool ==
    /\ stage = "denatured"
    /\ stage' = "cooled"
    /\ templateA' = templateA /\ hybridA' = hybridA /\ dnaA' = dnaA
    /\ primer' = primer /\ cycle' = cycle

AAnneal ==
    /\ stage = "cooled"
    /\ \E k \in 0..Min(primer, templateA) :
         /\ templateA' = templateA - k
         /\ hybridA' = hybridA + k
         /\ primer' = primer - k
    /\ dnaA' = dnaA
    /\ stage' = "annealed"
    /\ cycle' = cycle

AExtend ==
    /\ stage = "annealed"
    /\ dnaA' = dnaA + hybridA
    /\ hybridA' = 0
    /\ templateA' = templateA
    /\ primer' = primer
    /\ stage' = "extended"
    /\ cycle' = IF hybridA > 0 THEN cycle + 1 ELSE cycle

ANext == ADenature \/ ACool \/ AAnneal \/ AExtend

stagesSpec == AInit /\ [][ANext]_absVars

=============================================================================