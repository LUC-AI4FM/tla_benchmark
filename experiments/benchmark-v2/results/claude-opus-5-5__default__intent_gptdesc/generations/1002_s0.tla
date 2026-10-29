---------------------------- MODULE BarrierSync ----------------------------
(***************************************************************************)
(* Abstract model of a reusable (cyclic) barrier for N identical          *)
(* processes.                                                              *)
(*                                                                         *)
(* Each process repeats this cycle:                                        *)
(*   "work"    --Arrive--> "waiting" --Leave--> "work" (next round) ...    *)
(*                                                                         *)
(* Shared barrier state:                                                   *)
(*   gen     : barrier generation, the number of completed releases.       *)
(*             The barrier is "released" for round r exactly when          *)
(*             gen > r.                                                    *)
(*   arrived : the set of processes that have signalled arrival for the   *)
(*             current, not yet released, round (round number = gen).      *)
(*                                                                         *)
(* Per-process state:                                                      *)
(*   pc[p]    : local phase of p, either "work" or "waiting".              *)
(*   round[p] : the barrier round p is currently participating in.         *)
(*                                                                         *)
(* Release is one atomic step. It is enabled only when every process has   *)
(* arrived. It increments gen and resets arrived to {}, which makes the    *)
(* barrier reusable immediately. A process that is still waiting on round  *)
(* r can always tell that round r is released, because round[p] < gen.     *)
(* A process that has already re-arrived for round r+1 is recorded under   *)
(* the new generation. Rounds therefore cannot be confused.                *)
(*                                                                         *)
(* ASSUMPTIONS                                                             *)
(*  - N is a finite natural number with N > 0, and processes are 1..N.     *)
(*  - Steps are reliable. No process crashes, and no step is lost or       *)
(*    duplicated. Each step is atomic, and that includes Release.          *)
(*  - Interleaving semantics: one process or barrier step per transition.  *)
(*  - gen and round are unbounded naturals. For model checking with TLC,   *)
(*    use StateConstraint with a chosen MaxRound to bound the state space. *)
(*                                                                         *)
(* FAIRNESS                                                                *)
(*  - Weak fairness is sufficient. No strong fairness is needed.           *)
(*      * WF(Release): once all processes have arrived, Release stays      *)
(*        enabled. No process can leave and no process can re-arrive       *)
(*        until Release happens, so Release eventually occurs.             *)
(*      * WF(Leave(p)): once the barrier is released for p's round,        *)
(*        Leave(p) stays enabled until p takes it.                         *)
(*      * WF(Arrive(p)): working processes eventually reach the barrier.   *)
(*        This rules out permanent starvation or stalling of any process   *)
(*        and gives perpetual progress over infinitely many rounds.        *)
(*  - The conditional liveness property (all arrived ~> all released)      *)
(*    needs only WF on Release and Leave. The WF on Arrive is used only    *)
(*    for the unconditional progress properties.                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N,          \* number of processes
          MaxRound    \* used only by StateConstraint for bounded model checking

ASSUME NAssumption == N \in Nat /\ N > 0
ASSUME MaxRoundAssumption == MaxRound \in Nat

Procs  == 1..N
Phases == {"work", "waiting"}

VARIABLES pc,       \* pc[p] \in Phases
          round,    \* round[p] \in Nat
          arrived,  \* SUBSET Procs : arrivals for the current round gen
          gen       \* Nat : number of completed barrier releases

vars == <<pc, round, arrived, gen>>

---------------------------------------------------------------------------
Init ==
    /\ pc      = [p \in Procs |-> "work"]
    /\ round   = [p \in Procs |-> 0]
    /\ arrived = {}
    /\ gen     = 0

(* Process p reaches the barrier and signals arrival for its round.        *)
(* The invariant guarantees round[p] = gen whenever pc[p] = "work".        *)
Arrive(p) ==
    /\ pc[p] = "work"
    /\ pc'      = [pc EXCEPT ![p] = "waiting"]
    /\ arrived' = arrived \cup {p}
    /\ UNCHANGED <<round, gen>>

(* Atomic barrier release. Enabled only when all N processes have arrived  *)
(* for the current round. It resets the arrival set so the barrier can be  *)
(* reused.                                                                 *)
Release ==
    /\ arrived = Procs
    /\ gen'     = gen + 1
    /\ arrived' = {}
    /\ UNCHANGED <<pc, round>>

(* Process p passes the barrier into the post-barrier phase. This is only  *)
(* possible after the release of p's own round, i.e. round[p] < gen.       *)
Leave(p) ==
    /\ pc[p] = "waiting"
    /\ round[p] < gen
    /\ pc'    = [pc EXCEPT ![p] = "work"]
    /\ round' = [round EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<arrived, gen>>

Next ==
    \/ \E p \in Procs : Arrive(p)
    \/ Release
    \/ \E p \in Procs : Leave(p)

Fairness ==
    /\ WF_vars(Release)
    /\ \A p \in Procs : WF_vars(Leave(p))
    /\ \A p \in Procs : WF_vars(Arrive(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Spec without arrival fairness. This is enough for the conditional
\* liveness property BarrierLiveness.
SafetySpec == Init /\ [][Next]_vars /\ WF_vars(Release)
                   /\ \A p \in Procs : WF_vars(Leave(p))

---------------------------------------------------------------------------
(*************************** TYPE INVARIANTS *******************************)

TypeOK ==
    /\ pc      \in [Procs -> Phases]
    /\ round   \in [Procs -> Nat]
    /\ arrived \subseteq Procs
    /\ gen     \in Nat

\* Round bookkeeping stays well-formed. Every process is in the current
\* generation or exactly one behind it. A process can be one behind only
\* while it is waiting to leave an already released round.
RoundBoundsOK ==
    \A p \in Procs :
        /\ round[p] \in {gen, gen - 1} \cap Nat
        /\ (round[p] = gen - 1) => pc[p] = "waiting"
        /\ (pc[p] = "work") => round[p] = gen

---------------------------------------------------------------------------
(*************************** SAFETY ****************************************)

\* Core safety. If any process p has advanced past round r = round[q],
\* then every process q has arrived for round r and has not yet left it.
\* Processes are never more than one round apart.
BarrierSafety ==
    \A p, q \in Procs :
        round[p] > round[q] =>
            /\ round[p] = round[q] + 1
            /\ pc[q] = "waiting"

\* Action form. A release happens only when every process has signalled
\* arrival for the current round and is waiting at the barrier.
ReleaseOnlyWhenAllArrived ==
    [][Release => \A q \in Procs : pc[q] = "waiting" /\ round[q] = gen]_vars

\* Action form. A process leaves only after its own round has been
\* released. That release required all processes to arrive for that round.
LeaveOnlyAfterRelease ==
    [][\A p \in Procs : Leave(p) => round[p] < gen]_vars

\* Reusability and no confusion between rounds. The arrival set holds only
\* processes that arrived for the current, unreleased round. A process
\* still waiting on an old, released round is never counted as arrived.
ReusabilityInv ==
    /\ \A p \in arrived : pc[p] = "waiting" /\ round[p] = gen
    /\ \A p \in Procs :
          (pc[p] = "waiting" /\ round[p] = gen) <=> p \in arrived

\* The generation counter only moves forward, one step at a time.
GenMonotonic == [][gen' \in {gen, gen + 1}]_vars

Invariants ==
    /\ TypeOK
    /\ RoundBoundsOK
    /\ BarrierSafety
    /\ ReusabilityInv

---------------------------------------------------------------------------
(*************************** LIVENESS **************************************)

AllArrivedFor(r)  == \A p \in Procs : round[p] = r /\ pc[p] = "waiting"
AllReleasedFor(r) == \A p \in Procs : round[p] > r

\* Whenever all processes arrive for round r, all are eventually released
\* from round r. The quantifier ranges over Nat, which suits TLAPS proofs.
BarrierLiveness ==
    \A r \in Nat : AllArrivedFor(r) ~> AllReleasedFor(r)

\* TLC-checkable variant, bounded by MaxRound.
BarrierLivenessBounded ==
    \A r \in 0..MaxRound : AllArrivedFor(r) ~> AllReleasedFor(r)

\* Every waiting process is eventually let through. There is no permanent
\* blocking at the barrier.
NoStarvationAtBarrier ==
    \A p \in Procs : (pc[p] = "waiting") ~> (pc[p] = "work")

\* With arrival fairness, the barrier completes rounds forever and every
\* process makes progress infinitely often.
InfinitelyManyRounds == []<><<Release>>_vars
EveryProcessProgresses ==
    \A p \in Procs : []<><<Leave(p)>>_vars

---------------------------------------------------------------------------
(*************************** MODEL CHECKING AID ****************************)

\* Use as a TLC state constraint, not as part of Spec.
StateConstraint == gen <= MaxRound

THEOREM Spec => []Invariants
THEOREM Spec => ReleaseOnlyWhenAllArrived /\ LeaveOnlyAfterRelease /\ GenMonotonic
THEOREM Spec => BarrierLiveness /\ NoStarvationAtBarrier
THEOREM Spec => InfinitelyManyRounds /\ EveryProcessProgresses
=============================================================================