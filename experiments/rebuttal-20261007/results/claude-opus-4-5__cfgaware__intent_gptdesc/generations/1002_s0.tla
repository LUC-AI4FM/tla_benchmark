---------------------------- MODULE BarrierSync ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N > 0

VARIABLES
    procPhase,      \* procPhase[p] \in {"working", "arrived", "released"}
    barrierRound,   \* Current barrier round number (shared)
    procRound       \* procRound[p] = round number process p is participating in

vars == <<procPhase, barrierRound, procRound>>

Procs == 1..N

Phases == {"working", "arrived", "released"}

-----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ procPhase \in [Procs -> Phases]
    /\ barrierRound \in Nat
    /\ procRound \in [Procs -> Nat]

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ procPhase = [p \in Procs |-> "working"]
    /\ barrierRound = 0
    /\ procRound = [p \in Procs |-> 0]

-----------------------------------------------------------------------------
(* Process actions *)

(* A process in "working" phase arrives at the barrier for current round *)
Arrive(p) ==
    /\ procPhase[p] = "working"
    /\ procRound[p] = barrierRound
    /\ procPhase' = [procPhase EXCEPT ![p] = "arrived"]
    /\ UNCHANGED <<barrierRound, procRound>>

(* All processes have arrived - barrier releases all processes atomically *)
AllArrived == \A p \in Procs : procPhase[p] = "arrived"

Release ==
    /\ AllArrived
    /\ procPhase' = [p \in Procs |-> "released"]
    /\ UNCHANGED <<barrierRound, procRound>>

(* A released process proceeds to working state for next round *)
Proceed(p) ==
    /\ procPhase[p] = "released"
    /\ procPhase' = [procPhase EXCEPT ![p] = "working"]
    /\ procRound' = [procRound EXCEPT ![p] = barrierRound + 1]
    /\ barrierRound' = IF \A q \in Procs \ {p} : procPhase[q] = "working"
                       THEN barrierRound + 1
                       ELSE barrierRound

-----------------------------------------------------------------------------
(* Next state relation *)

Next ==
    \/ \E p \in Procs : Arrive(p)
    \/ Release
    \/ \E p \in Procs : Proceed(p)

-----------------------------------------------------------------------------
(* Fairness conditions *)
(* 
   We require weak fairness on all process actions to ensure liveness:
   - Each process will eventually arrive if continuously enabled
   - The release will eventually happen if all have arrived
   - Each process will eventually proceed after release
   
   Assumptions:
   - N is finite and positive
   - All process steps are reliable (no crashes)
   - Weak fairness suffices since enabled actions remain enabled until taken
*)

Fairness ==
    /\ \A p \in Procs : WF_vars(Arrive(p))
    /\ WF_vars(Release)
    /\ \A p \in Procs : WF_vars(Proceed(p))

-----------------------------------------------------------------------------
(* Complete specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety property: No process is released until all have arrived *)
(* This is captured by the fact that Release requires AllArrived *)
(* We express it as: if any process is released, all must be released together *)

SafetyInvariant ==
    \A p \in Procs :
        procPhase[p] = "released" => \A q \in Procs : procPhase[q] # "working"

(* Additional safety: processes in same round are synchronized *)
RoundConsistency ==
    \A p, q \in Procs :
        (procPhase[p] = "arrived" /\ procPhase[q] = "arrived") =>
            procRound[p] = procRound[q]

-----------------------------------------------------------------------------
(* Liveness property: If all processes eventually arrive, they will be released *)

LivenessProperty ==
    [](AllArrived => <>(\A p \in Procs : procPhase[p] = "released"))

(* Stronger liveness: Every process that arrives will eventually proceed *)
ProgressProperty ==
    \A p \in Procs : [](procPhase[p] = "arrived" ~> procPhase[p] = "working")

-----------------------------------------------------------------------------
(* Combined barrier property for model checking *)

BarrierProperty ==
    /\ TypeOK
    /\ SafetyInvariant
    /\ RoundConsistency

=============================================================================