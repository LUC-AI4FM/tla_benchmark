------------------------------ MODULE CyclicAmplification ------------------------------
(***************************************************************************)
(* A model of a cyclic molecular amplification process, similar to PCR.    *)
(*                                                                         *)
(* Molecular species (all counted as natural numbers):                     *)
(*   p       : free primer molecules                                       *)
(*   tOrig   : single-stranded original templates (undefined ends)         *)
(*   tLong   : single strands with one primer-defined end                  *)
(*   tShort  : single strands with both ends primer-defined (target size)  *)
(*   hOrig, hLong, hShort : primer/template hybrids on each template kind  *)
(*   dsOrig  : original double strands (tOrig + tOrig)                     *)
(*   dsOL    : double strand tOrig + tLong                                 *)
(*   dsLS    : double strand tLong + tShort                                *)
(*   dsShort : double strand tShort + tShort = the small final product     *)
(*                                                                         *)
(* Phases: denature (hot) -> cool (ready) -> anneal -> extend -> ...       *)
(* The exact-size product can first appear at the extension of cycle 3.    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    InitDS,        \* initial number of original double strands
    InitPrimers,   \* initial number of primer molecules
    MaxCycle,      \* number of cycles the process runs
    Threshold      \* cycle threshold before which no product may exist

ASSUME /\ InitDS \in Nat
       /\ InitPrimers \in Nat
       /\ MaxCycle \in Nat
       /\ Threshold \in Nat
       /\ Threshold <= 3

VARIABLES
    p, tOrig, tLong, tShort,
    hOrig, hLong, hShort,
    dsOrig, dsOL, dsLS, dsShort,
    stage, temp, cycle

counts == <<p, tOrig, tLong, tShort, hOrig, hLong, hShort,
            dsOrig, dsOL, dsLS, dsShort>>
vars == <<p, tOrig, tLong, tShort, hOrig, hLong, hShort,
          dsOrig, dsOL, dsLS, dsShort, stage, temp, cycle>>

Stages == {"denatured", "ready", "annealed", "extended"}
Temps  == {"hot", "cool", "warm"}

Product == dsShort

Hybrids == hOrig + hLong + hShort
Doubles == dsOrig + dsOL + dsLS + dsShort

(* Total mass in units of strands/primers: each hybrid and each double     *)
(* strand consists of two units.                                           *)
TotalMass == p + tOrig + tLong + tShort + 2 * Hybrids + 2 * Doubles
InitMass  == InitPrimers + 2 * InitDS

(* Original strands are never created nor destroyed. *)
OrigStrands == tOrig + hOrig + 2 * dsOrig + dsOL

-----------------------------------------------------------------------------

Init ==
    /\ p = InitPrimers
    /\ tOrig = 0 /\ tLong = 0 /\ tShort = 0
    /\ hOrig = 0 /\ hLong = 0 /\ hShort = 0
    /\ dsOrig = InitDS
    /\ dsOL = 0 /\ dsLS = 0 /\ dsShort = 0
    /\ stage = "extended"
    /\ temp = "warm"
    /\ cycle = 0

(* High-temperature denaturation: all double strands separate fully into  *)
(* single templates; hybrids release their primers and templates.         *)
Denature ==
    /\ stage = "extended"
    /\ cycle < MaxCycle
    /\ tOrig'  = tOrig  + 2 * dsOrig + dsOL + hOrig
    /\ tLong'  = tLong  + dsOL + dsLS + hLong
    /\ tShort' = tShort + dsLS + 2 * dsShort + hShort
    /\ p'      = p + hOrig + hLong + hShort
    /\ hOrig' = 0 /\ hLong' = 0 /\ hShort' = 0
    /\ dsOrig' = 0 /\ dsOL' = 0 /\ dsLS' = 0 /\ dsShort' = 0
    /\ stage' = "denatured"
    /\ temp' = "hot"
    /\ UNCHANGED cycle

(* Cooling to the annealing temperature. *)
Cool ==
    /\ stage = "denatured"
    /\ stage' = "ready"
    /\ temp' = "cool"
    /\ UNCHANGED <<counts, cycle>>

(* Annealing: primers bind to a nondeterministically chosen number of      *)
(* available templates of each kind, bounded by available primers.         *)
AnnealWith(kO, kL, kS) ==
    /\ kO + kL + kS <= p
    /\ p'      = p - (kO + kL + kS)
    /\ tOrig'  = tOrig - kO
    /\ tLong'  = tLong - kL
    /\ tShort' = tShort - kS
    /\ hOrig'  = hOrig + kO
    /\ hLong'  = hLong + kL
    /\ hShort' = hShort + kS
    /\ UNCHANGED <<dsOrig, dsOL, dsLS, dsShort>>

Anneal ==
    /\ stage = "ready"
    /\ \E kO \in 0..tOrig, kL \in 0..tLong, kS \in 0..tShort :
           AnnealWith(kO, kL, kS)
    /\ stage' = "annealed"
    /\ temp' = "cool"
    /\ UNCHANGED cycle

(* Extension: every hybrid is extended into the corresponding double     *)
(* strand; extension on a short template yields the final product.       *)
Extend ==
    /\ stage = "annealed"
    /\ dsOL'    = dsOL + hOrig
    /\ dsLS'    = dsLS + hLong
    /\ dsShort' = dsShort + hShort
    /\ hOrig' = 0 /\ hLong' = 0 /\ hShort' = 0
    /\ UNCHANGED <<p, tOrig, tLong, tShort, dsOrig>>
    /\ stage' = "extended"
    /\ temp' = "warm"
    /\ cycle' = cycle + 1

(* Terminal stuttering after the final cycle. *)
Done ==
    /\ stage = "extended"
    /\ cycle >= MaxCycle
    /\ UNCHANGED vars

Next == Denature \/ Cool \/ Anneal \/ Extend \/ Done

Fairness ==
    /\ WF_vars(Denature)
    /\ WF_vars(Cool)
    /\ WF_vars(Anneal)
    /\ WF_vars(Extend)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ p \in Nat /\ tOrig \in Nat /\ tLong \in Nat /\ tShort \in Nat
    /\ hOrig \in Nat /\ hLong \in Nat /\ hShort \in Nat
    /\ dsOrig \in Nat /\ dsOL \in Nat /\ dsLS \in Nat /\ dsShort \in Nat
    /\ stage \in Stages
    /\ temp \in Temps
    /\ cycle \in Nat

MassConserved == TotalMass = InitMass

OrigConserved == OrigStrands = 2 * InitDS

PrimersBounded == p <= InitPrimers

(* After denaturation (and while ready) no doubles or hybrids remain. *)
DenatureComplete ==
    stage \in {"denatured", "ready"} => (Doubles = 0 /\ Hybrids = 0)

(* Hybrids exist only between annealing and extension. *)
HybridsOnlyWhenAnnealed ==
    stage # "annealed" => Hybrids = 0

StageTempConsistent ==
    /\ stage = "denatured" => temp = "hot"
    /\ stage \in {"ready", "annealed"} => temp = "cool"
    /\ stage = "extended" => temp = "warm"

CycleBounded == cycle <= MaxCycle

(* No premature product before the threshold cycle. *)
NoEarlyProduct == cycle < Threshold => Product = 0

NoShortStrandsEarly == cycle < 2 => (tShort = 0 /\ hShort = 0 /\ dsLS = 0 /\ Product = 0)

Inv ==
    /\ TypeOK
    /\ MassConserved
    /\ OrigConserved
    /\ PrimersBounded
    /\ DenatureComplete
    /\ HybridsOnlyWhenAnnealed
    /\ StageTempConsistent
    /\ CycleBounded
    /\ NoEarlyProduct

-----------------------------------------------------------------------------
(* Action properties *)

StageOrder ==
    [][stage' # stage =>
         <<stage, stage'>> \in { <<"extended", "denatured">>,
                                 <<"denatured", "ready">>,
                                 <<"ready", "annealed">>,
                                 <<"annealed", "extended">> }]_vars

CycleIncrementsOnlyOnExtend ==
    [][cycle' # cycle =>
         /\ stage = "annealed"
         /\ stage' = "extended"
         /\ cycle' = cycle + 1]_vars

PrimersConsumedOnlyInAnneal ==
    [][p' < p => (stage = "ready" /\ stage' = "annealed")]_vars

NoPrimerOverconsumption ==
    [][(stage = "ready" /\ stage' = "annealed") =>
         /\ p - p' <= p
         /\ tOrig - tOrig' <= tOrig
         /\ tLong - tLong' <= tLong
         /\ tShort - tShort' <= tShort
         /\ (tOrig - tOrig') + (tLong - tLong') + (tShort - tShort') = p - p']_vars

MassPreserved == [][TotalMass' = TotalMass]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

EventuallyAllCycles == <>(cycle = MaxCycle)

DenatureProgress == (stage = "extended" /\ cycle < MaxCycle) ~> (stage = "denatured")
CoolProgress     == (stage = "denatured") ~> (stage = "ready")
AnnealProgress   == (stage = "ready") ~> (stage = "annealed")
ExtendProgress   == (stage = "annealed") ~> (stage = "extended")

Liveness ==
    /\ EventuallyAllCycles
    /\ DenatureProgress
    /\ CoolProgress
    /\ AnnealProgress
    /\ ExtendProgress

THEOREM Spec => []Inv
THEOREM Spec => StageOrder /\ CycleIncrementsOnlyOnExtend /\ MassPreserved
THEOREM Spec => Liveness
=============================================================================