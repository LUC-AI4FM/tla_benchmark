------------------------------- MODULE PCR -------------------------------
(***************************************************************************)
(* PCR (Polymerase Chain Reaction) thermal cycling.                        *)
(*                                                                         *)
(* Molecular species (counts):                                             *)
(*   dna      : double-stranded DNA molecules                              *)
(*   template : single-stranded template strands                           *)
(*   primer   : free primers                                               *)
(*   hybrid   : primer-template hybrids (one template strand + one primer) *)
(*                                                                         *)
(* Protocol: init -> (denaturing -> annealing -> extending)^MaxCycles      *)
(*           -> done                                                       *)
(* Each step changes the temperature to the stage's temperature and        *)
(* performs that stage's reaction.                                         *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS InitDNA,      \* initial number of double-stranded DNA molecules
          InitPrimers,  \* initial number of free primers
          MaxCycles     \* number of thermal cycles in the protocol

ASSUME /\ InitDNA \in Nat
       /\ InitPrimers \in Nat
       /\ MaxCycles \in Nat

VARIABLES temp, dna, template, primer, hybrid, stage, cycle

vars == <<temp, dna, template, primer, hybrid, stage, cycle>>

---------------------------------------------------------------------------
(* Temperatures in degrees Celsius *)
RoomTemp     == 25
AnnealTemp   == 55
ExtendTemp   == 72
DenatureTemp == 95

Temps  == {RoomTemp, AnnealTemp, ExtendTemp, DenatureTemp}
Stages == {"init", "denaturing", "annealing", "extending", "done"}

StageTemp(s) ==
    CASE s = "init"       -> RoomTemp
      [] s = "denaturing" -> DenatureTemp
      [] s = "annealing"  -> AnnealTemp
      [] s = "extending"  -> ExtendTemp
      [] s = "done"       -> RoomTemp

Min(a, b) == IF a <= b THEN a ELSE b

\* Legal stage-to-stage transitions of the protocol
ValidStageSteps ==
    { <<"init", "denaturing">>,
      <<"init", "done">>,
      <<"denaturing", "annealing">>,
      <<"annealing", "extending">>,
      <<"extending", "denaturing">>,
      <<"extending", "done">> }

\* Conserved quantity: every primer is a potential strand
TotalUnits == 2 * InitDNA + InitPrimers
Units == 2 * dna + template + 2 * hybrid + primer

\* Number of DNA strands present (a hybrid contains one template strand)
Strands == 2 * dna + template + hybrid

---------------------------------------------------------------------------
TypeOK ==
    /\ temp \in Temps
    /\ dna \in Nat
    /\ template \in Nat
    /\ primer \in Nat
    /\ hybrid \in Nat
    /\ stage \in Stages
    /\ cycle \in 0..MaxCycles

Init ==
    /\ temp = RoomTemp
    /\ dna = InitDNA
    /\ template = 0
    /\ primer = InitPrimers
    /\ hybrid = 0
    /\ stage = "init"
    /\ cycle = 0

(* High temperature: double strands separate into two single strands;  *)
(* any primer-template hybrids melt as well.                           *)
Denature ==
    /\ stage \in {"init", "extending"}
    /\ cycle < MaxCycles
    /\ temp' = DenatureTemp
    /\ template' = template + 2 * dna + hybrid
    /\ primer' = primer + hybrid
    /\ dna' = 0
    /\ hybrid' = 0
    /\ stage' = "denaturing"
    /\ UNCHANGED cycle

(* Lower temperature: primers bind to single-stranded templates. *)
Anneal ==
    /\ stage = "denaturing"
    /\ LET k == Min(template, primer) IN
         /\ hybrid' = hybrid + k
         /\ template' = template - k
         /\ primer' = primer - k
    /\ temp' = AnnealTemp
    /\ stage' = "annealing"
    /\ UNCHANGED <<dna, cycle>>

(* Polymerase extends each hybrid into a full double-stranded molecule; *)
(* this completes one amplification cycle.                              *)
Extend ==
    /\ stage = "annealing"
    /\ temp' = ExtendTemp
    /\ dna' = dna + hybrid
    /\ hybrid' = 0
    /\ stage' = "extending"
    /\ cycle' = cycle + 1
    /\ UNCHANGED <<template, primer>>

(* Protocol finished: cool down to hold temperature. *)
Finish ==
    /\ stage \in {"init", "extending"}
    /\ cycle = MaxCycles
    /\ temp' = RoomTemp
    /\ stage' = "done"
    /\ UNCHANGED <<dna, template, primer, hybrid, cycle>>

(* Terminal state: stutter to avoid spurious deadlock. *)
Terminated ==
    /\ stage = "done"
    /\ UNCHANGED vars

Next == Denature \/ Anneal \/ Extend \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

---------------------------------------------------------------------------
(* Safety invariants *)

\* Molecular quantities never negative
NonNegative ==
    /\ dna >= 0 /\ template >= 0 /\ primer >= 0 /\ hybrid >= 0

\* Temperature always matches the current stage
TempMatchesStage == temp = StageTemp(stage)

\* Conservation of material (strands + primers)
Conservation == Units = TotalUnits

\* Primers are only ever consumed
PrimerBound == primer <= InitPrimers

\* Stage-dependent molecular state
StageMolecularState ==
    /\ stage = "init"       => /\ dna = InitDNA /\ template = 0
                               /\ hybrid = 0 /\ primer = InitPrimers
    /\ stage = "denaturing" => /\ dna = 0 /\ hybrid = 0
    /\ stage = "annealing"  => /\ dna = 0
                               /\ (template = 0 \/ primer = 0)
    /\ stage = "extending"  => hybrid = 0
    /\ stage = "done"       => hybrid = 0

\* Cycle count is consistent with the protocol position
CycleConsistency ==
    /\ cycle \in 0..MaxCycles
    /\ stage = "init" => cycle = 0
    /\ stage = "extending" => cycle >= 1
    /\ stage \in {"denaturing", "annealing"} => cycle < MaxCycles
    /\ stage = "done" => cycle = MaxCycles

\* Amplification is at most exponential in the number of cycles
AmplificationBound == Strands <= 2 * InitDNA * (2 ^ cycle)

\* Strands are never lost
StrandsNeverLost == Strands >= 2 * InitDNA

Invariants ==
    /\ TypeOK
    /\ NonNegative
    /\ TempMatchesStage
    /\ Conservation
    /\ PrimerBound
    /\ StageMolecularState
    /\ CycleConsistency
    /\ AmplificationBound
    /\ StrandsNeverLost

---------------------------------------------------------------------------
(* Action (step) properties *)

\* Stages follow the PCR protocol order
ValidStageSequence ==
    [][stage' # stage => <<stage, stage'>> \in ValidStageSteps]_stage

\* Cycle counter only increments by one, and only upon extension
CycleIncrementsOnExtension ==
    [][cycle' # cycle => /\ cycle' = cycle + 1
                         /\ stage = "annealing"
                         /\ stage' = "extending"]_cycle

\* Molecular changes are consistent with the reaction of each stage
MolecularConsistency ==
    [][ /\ (stage' = "denaturing" /\ stage # "denaturing") =>
             /\ temp' = DenatureTemp
             /\ dna' = 0 /\ hybrid' = 0
             /\ template' = template + 2 * dna + hybrid
             /\ primer' = primer + hybrid
        /\ (stage' = "annealing" /\ stage # "annealing") =>
             /\ temp' = AnnealTemp
             /\ dna' = dna
             /\ hybrid' >= hybrid
             /\ primer - primer' = hybrid' - hybrid
             /\ template - template' = hybrid' - hybrid
        /\ (stage' = "extending" /\ stage # "extending") =>
             /\ temp' = ExtendTemp
             /\ dna' = dna + hybrid
             /\ hybrid' = 0
             /\ primer' = primer
             /\ template' = template
        /\ (stage' = "done" /\ stage # "done") =>
             /\ UNCHANGED <<dna, template, primer, hybrid>>
      ]_vars

\* DNA melts only at high temperature; primers anneal only at annealing temp
TemperatureDrivenTransitions ==
    [][ /\ (dna' < dna) => temp' = DenatureTemp
        /\ (hybrid' > hybrid) => temp' = AnnealTemp
        /\ (dna' > dna) => temp' = ExtendTemp ]_vars

---------------------------------------------------------------------------
(* Liveness *)

\* The protocol eventually completes
EventuallyDone == <>(stage = "done")

\* All cycles are eventually completed
AllCyclesComplete == <>(cycle = MaxCycles)

\* Once done, it stays done
DoneIsStable == [](stage = "done" => [](stage = "done"))

\* Every denaturation is eventually followed by an extension
DenatureLeadsToExtend == (stage = "denaturing") ~> (stage = "extending")

---------------------------------------------------------------------------
THEOREM Spec => []Invariants
THEOREM Spec => ValidStageSequence /\ CycleIncrementsOnExtension
THEOREM Spec => MolecularConsistency /\ TemperatureDrivenTransitions
THEOREM Spec => EventuallyDone /\ AllCyclesComplete /\ DenatureLeadsToExtend
=============================================================================