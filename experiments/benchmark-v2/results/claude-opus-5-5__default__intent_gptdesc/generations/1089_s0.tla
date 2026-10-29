---------------------------- MODULE PCRProtocol ----------------------------
(***************************************************************************)
(* A staged, cyclic biochemical amplification protocol.                    *)
(*                                                                         *)
(* Molecules is a finite pool of strand identities.                        *)
(*   - InitTemplates are the strands present initially.                    *)
(*   - Every other identity is an unused "slot" ("Absent").                *)
(*   - Extension may turn a slot into a newly synthesized product strand.  *)
(*   - This is the only way new strands are created, and strands are never *)
(*     destroyed.                                                          *)
(*                                                                         *)
(* Primers are individual primer molecules.                                *)
(*   - A primer is Free, Bound (hybridized to exactly one strand), or      *)
(*     Consumed (incorporated into a new strand by extension).             *)
(*   - Bound primers that were not extended are recycled at reset.         *)
(*                                                                         *)
(* Each cycle runs through the stages Bind -> Extend -> Reset.             *)
(*   - Within a stage, the choice of which primer pairs with which strand  *)
(*     is nondeterministic.                                                *)
(*   - How many interactions occur before the stage ends is also           *)
(*     nondeterministic.                                                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Molecules,      \* finite pool of strand identities
    InitTemplates,  \* strands present initially
    Primers,        \* finite set of primer molecules
    Compatible,     \* allowed (primer, strand) hybridization pairs
    MaxCycles,      \* number of cycles the protocol runs
    NoPrimer        \* marker meaning "no primer bound"

ASSUME
    /\ IsFiniteSet(Molecules)
    /\ IsFiniteSet(Primers)
    /\ InitTemplates \subseteq Molecules
    /\ Compatible \subseteq (Primers \X Molecules)
    /\ MaxCycles \in Nat
    /\ NoPrimer \notin Primers

VARIABLES
    tstate,    \* tstate[m] \in StrandStates
    pstate,    \* pstate[p] \in PrimerStates
    bindOf,    \* bindOf[m]: primer hybridized to strand m, or NoPrimer
    stage,     \* current protocol stage
    cycle,     \* index of the current / last started cycle
    produced   \* total number of amplified product strands synthesized

vars == <<tstate, pstate, bindOf, stage, cycle, produced>>

(***************************************************************************)
(* Strand states:                                                          *)
(*   "Absent"   : identity not (yet) in existence                          *)
(*   "Free"     : single-stranded, available as a template                 *)
(*   "Bound"    : hybridized with exactly one primer                       *)
(*   "Extended" : primer extended along it (duplex template side)          *)
(*   "Product"  : newly synthesized amplified strand from this cycle       *)
(***************************************************************************)
StrandStates == {"Absent", "Free", "Bound", "Extended", "Product"}
PrimerStates == {"Free", "Bound", "Consumed"}
Stages       == {"Idle", "Bind", "Extend", "Reset"}

Present    == {m \in Molecules : tstate[m] # "Absent"}
BoundMols  == {m \in Molecules : tstate[m] = "Bound"}
FreeSlots  == {m \in Molecules : tstate[m] = "Absent"}
FreePrims  == {p \in Primers : pstate[p] = "Free"}
BoundPrims == {p \in Primers : pstate[p] = "Bound"}
UsedPrims  == {p \in Primers : pstate[p] = "Consumed"}

\* A compatible free primer / free strand pair exists.
CanBind ==
    \E m \in Molecules, p \in Primers :
        /\ tstate[m] = "Free"
        /\ pstate[p] = "Free"
        /\ <<p, m>> \in Compatible

\* Room remains for a newly synthesized strand.
CanGrow == FreeSlots # {}

-----------------------------------------------------------------------------
TypeOK ==
    /\ tstate \in [Molecules -> StrandStates]
    /\ pstate \in [Primers -> PrimerStates]
    /\ bindOf \in [Molecules -> Primers \cup {NoPrimer}]
    /\ stage \in Stages
    /\ cycle \in 0..MaxCycles
    /\ produced \in 0..Cardinality(Molecules)

Init ==
    /\ tstate = [m \in Molecules |->
                    IF m \in InitTemplates THEN "Free" ELSE "Absent"]
    /\ pstate = [p \in Primers |-> "Free"]
    /\ bindOf = [m \in Molecules |-> NoPrimer]
    /\ stage = "Idle"
    /\ cycle = 0
    /\ produced = 0

-----------------------------------------------------------------------------
(* Begin a new cycle. *)
StartCycle ==
    /\ stage = "Idle"
    /\ cycle < MaxCycles
    /\ stage' = "Bind"
    /\ cycle' = cycle + 1
    /\ UNCHANGED <<tstate, pstate, bindOf, produced>>

(* Annealing: a free primer hybridizes to a compatible free strand. *)
BindPrimer ==
    /\ stage = "Bind"
    /\ \E m \in Molecules, p \in Primers :
          /\ tstate[m] = "Free"
          /\ pstate[p] = "Free"
          /\ <<p, m>> \in Compatible
          /\ tstate' = [tstate EXCEPT ![m] = "Bound"]
          /\ pstate' = [pstate EXCEPT ![p] = "Bound"]
          /\ bindOf' = [bindOf EXCEPT ![m] = p]
    /\ UNCHANGED <<stage, cycle, produced>>

EndBind ==
    /\ stage = "Bind"
    /\ stage' = "Extend"
    /\ UNCHANGED <<tstate, pstate, bindOf, cycle, produced>>

(***************************************************************************)
(* Extension: a bound primer is extended into a new complementary strand.  *)
(*   - The primer is consumed (incorporated into the new strand).          *)
(*   - The new strand occupies a previously absent slot.                   *)
(*   - Extension is the only action that creates molecules.                *)
(***************************************************************************)
ExtendPrimer ==
    /\ stage = "Extend"
    /\ \E m \in Molecules, n \in Molecules :
          /\ tstate[m] = "Bound"
          /\ tstate[n] = "Absent"
          /\ tstate' = [tstate EXCEPT ![m] = "Extended", ![n] = "Product"]
          /\ pstate' = [pstate EXCEPT ![bindOf[m]] = "Consumed"]
          /\ bindOf' = [bindOf EXCEPT ![m] = NoPrimer]
    /\ produced' = produced + 1
    /\ UNCHANGED <<stage, cycle>>

EndExtend ==
    /\ stage = "Extend"
    /\ stage' = "Reset"
    /\ UNCHANGED <<tstate, pstate, bindOf, cycle, produced>>

(***************************************************************************)
(* Reset / denaturation and cleanup.                                       *)
(*   - Duplexes separate.                                                  *)
(*   - Products and old templates all become free templates.               *)
(*   - Unextended primers dissociate and are recycled.                     *)
(*   - Consumed primers stay consumed.                                     *)
(***************************************************************************)
ResetStage ==
    /\ stage = "Reset"
    /\ tstate' = [m \in Molecules |->
                    IF tstate[m] = "Absent" THEN "Absent" ELSE "Free"]
    /\ pstate' = [p \in Primers |->
                    IF pstate[p] = "Bound" THEN "Free" ELSE pstate[p]]
    /\ bindOf' = [m \in Molecules |-> NoPrimer]
    /\ stage' = "Idle"
    /\ UNCHANGED <<cycle, produced>>

(* Protocol finished: stutter. *)
Done ==
    /\ stage = "Idle"
    /\ cycle = MaxCycles
    /\ UNCHANGED vars

Next ==
    \/ StartCycle
    \/ BindPrimer
    \/ EndBind
    \/ ExtendPrimer
    \/ EndExtend
    \/ ResetStage
    \/ Done

Fairness ==
    /\ WF_vars(StartCycle)
    /\ WF_vars(EndBind)
    /\ WF_vars(EndExtend)
    /\ WF_vars(ResetStage)
    /\ SF_vars(BindPrimer)
    /\ SF_vars(ExtendPrimer)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(*************************** SAFETY PROPERTIES ****************************)

\* A primer binds only to a compatible strand, and binding is recorded consistently.
CompatibleBinding ==
    \A m \in Molecules :
        /\ (tstate[m] = "Bound") <=> (bindOf[m] # NoPrimer)
        /\ tstate[m] = "Bound" =>
              /\ <<bindOf[m], m>> \in Compatible
              /\ pstate[bindOf[m]] = "Bound"

\* A strand is never bound by more than one primer, and a primer is never bound to more than one strand.
ExclusiveBinding ==
    /\ \A m1, m2 \in BoundMols : bindOf[m1] = bindOf[m2] => m1 = m2
    /\ \A p \in Primers :
          pstate[p] = "Bound" <=> (\E m \in Molecules : bindOf[m] = p)

\* Binding and extension occur only in their stages.
StageConsistency ==
    /\ stage \in {"Idle", "Bind"} =>
          \A m \in Molecules : tstate[m] \in {"Absent", "Free", "Bound"}
    /\ stage = "Idle" =>
          /\ BoundMols = {}
          /\ BoundPrims = {}

-------------------------- CONSERVATION ----------------------------------

\* Strands are only created by extension, one per extension.
StrandConservation ==
    Cardinality(Present) = Cardinality(InitTemplates) + produced

\* Each extension consumes exactly one primer.
\* Bound primers match bound strands one-to-one.
\* Primers are never created or destroyed.
PrimerConservation ==
    /\ Cardinality(UsedPrims) = produced
    /\ Cardinality(BoundPrims) = Cardinality(BoundMols)
    /\ Cardinality(FreePrims) + Cardinality(BoundPrims)
         + Cardinality(UsedPrims) = Cardinality(Primers)

\* Initial templates never disappear.
TemplatesPersist ==
    \A m \in InitTemplates : tstate[m] # "Absent"

Invariants ==
    /\ TypeOK
    /\ CompatibleBinding
    /\ ExclusiveBinding
    /\ StageConsistency
    /\ StrandConservation
    /\ PrimerConservation
    /\ TemplatesPersist

\* Allowed transformations only:
\*   - product count never decreases;
\*   - it grows by exactly one, and only through extension;
\*   - existing strands never vanish;
\*   - consumed primers are never regenerated.
MonotoneProduction ==
    [][ /\ produced' \in {produced, produced + 1}
        /\ (produced' = produced + 1) => (stage = "Extend")
        /\ \A m \in Molecules :
              tstate[m] # "Absent" => tstate'[m] # "Absent"
        /\ \A p \in Primers :
              pstate[p] = "Consumed" => pstate'[p] = "Consumed"
      ]_vars

\* Stage progression follows Idle -> Bind -> Extend -> Reset -> Idle.
StageOrder ==
    [][ stage' # stage =>
          \/ stage = "Idle"   /\ stage' = "Bind"
          \/ stage = "Bind"   /\ stage' = "Extend"
          \/ stage = "Extend" /\ stage' = "Reset"
          \/ stage = "Reset"  /\ stage' = "Idle"
      ]_vars

-----------------------------------------------------------------------------
(*************************** LIVENESS PROPERTIES **************************)

\* Progress: every started cycle eventually completes all of its stages.
CycleProgress ==
    \A c \in 1..MaxCycles :
        (cycle = c /\ stage # "Idle") ~> (cycle = c /\ stage = "Idle")

\* The protocol eventually completes all of its cycles.
ProtocolCompletes ==
    <>(cycle = MaxCycles /\ stage = "Idle")

(***************************************************************************)
(* Amplification liveness.                                                 *)
(*   Premise: across cycles, the Bind stage repeatedly sees a compatible   *)
(*   free primer/strand pair and room for new strands.                     *)
(*   Conclusion: new amplified products are eventually produced.           *)
(***************************************************************************)
AmplificationLiveness ==
    ([]<>(stage = "Bind" /\ CanBind /\ CanGrow)) =>
        \A n \in 0..Cardinality(Molecules) :
            [](produced = n => <>(produced > n))

\* Weaker form: some product is eventually made.
EventualAmplification ==
    ([]<>(stage = "Bind" /\ CanBind /\ CanGrow)) => <>(produced > 0)

-----------------------------------------------------------------------------
THEOREM Spec => []Invariants
THEOREM Spec => MonotoneProduction /\ StageOrder
THEOREM Spec => CycleProgress /\ ProtocolCompletes
THEOREM Spec => AmplificationLiveness /\ EventualAmplification
=============================================================================