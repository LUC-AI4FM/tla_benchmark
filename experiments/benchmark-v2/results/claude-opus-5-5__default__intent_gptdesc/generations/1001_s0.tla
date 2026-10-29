---------------------------- MODULE ReusableBarrier ----------------------------
(***************************************************************************)
(* A reusable barrier for N concurrent processes with arbitrary process    *)
(* identities.  Each process repeatedly works locally, arrives at the      *)
(* barrier, waits until all N processes have arrived at that same barrier  *)
(* instance, is released, and then starts the next phase.                  *)
(*                                                                         *)
(* Steps interleave asynchronously.  There is no shared clock, so          *)
(* processes may run at arbitrary relative speeds.  Phase and instance     *)
(* numbers are unbounded.                                                  *)
(*                                                                         *)
(* The shared control is only abstract barrier state:                      *)
(*   gen     - the current barrier instance (generation) number            *)
(*   arrived - the set of processes that have arrived at instance gen      *)
(* This abstraction does not commit to an implementation strategy.        *)
(* Sense reversal, counters, and tree barriers all refine it.             *)
(*                                                                         *)
(* lastArrived is a history (ghost) variable.  It records the barrier      *)
(* instance at which each process most recently arrived.  It is used only  *)
(* to state the safety properties.                                         *)
(***************************************************************************)
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS Proc,   \* arbitrary set of process identities
          N       \* number of processes

ASSUME ProcAssump == /\ IsFiniteSet(Proc)
                     /\ N \in Nat \ {0}
                     /\ Cardinality(Proc) = N

VARIABLES pc,          \* pc[p] \in {"working","waiting","released"}
          myPhase,     \* myPhase[p] : barrier instance p is currently in
          gen,         \* shared: current (open) barrier instance number
          arrived,     \* shared: processes arrived at instance gen
          lastArrived  \* ghost: last instance each process arrived at

vars == <<pc, myPhase, gen, arrived, lastArrived>>

States == {"working", "waiting", "released"}

-----------------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> States]
  /\ myPhase \in [Proc -> Nat]
  /\ gen \in Nat
  /\ arrived \in SUBSET Proc
  /\ lastArrived \in [Proc -> Nat \cup {-1}]

Init ==
  /\ pc = [p \in Proc |-> "working"]
  /\ myPhase = [p \in Proc |-> 0]
  /\ gen = 0
  /\ arrived = {}
  /\ lastArrived = [p \in Proc |-> -1]

(* Process p finishes its local work and arrives at its barrier instance. *)
Arrive(p) ==
  /\ pc[p] = "working"
  /\ myPhase[p] = gen
  /\ pc' = [pc EXCEPT ![p] = "waiting"]
  /\ arrived' = arrived \cup {p}
  /\ lastArrived' = [lastArrived EXCEPT ![p] = myPhase[p]]
  /\ UNCHANGED <<myPhase, gen>>

(* The barrier instance completes once all N processes have arrived.     *)
(* This opens the next instance with an empty arrival set.               *)
Complete ==
  /\ Cardinality(arrived) = N
  /\ gen' = gen + 1
  /\ arrived' = {}
  /\ UNCHANGED <<pc, myPhase, lastArrived>>

(* A waiting process observes that its instance has completed and is     *)
(* released.                                                             *)
Leave(p) ==
  /\ pc[p] = "waiting"
  /\ gen > myPhase[p]
  /\ pc' = [pc EXCEPT ![p] = "released"]
  /\ UNCHANGED <<myPhase, gen, arrived, lastArrived>>

(* A released process begins local work in its next phase.               *)
Resume(p) ==
  /\ pc[p] = "released"
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ myPhase' = [myPhase EXCEPT ![p] = myPhase[p] + 1]
  /\ UNCHANGED <<gen, arrived, lastArrived>>

ProcStep(p) == Arrive(p) \/ Leave(p) \/ Resume(p)

Next == Complete \/ \E p \in Proc : ProcStep(p)

(* Fair scheduling: each process, and the barrier control, is weakly fair. *)
Fairness == /\ WF_vars(Complete)
            /\ \A p \in Proc : WF_vars(ProcStep(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Counting and phase invariants                                           *)
(***************************************************************************)

ArrivalCount == Cardinality(arrived)

CountInv ==
  /\ ArrivalCount <= N
  /\ ArrivalCount = Cardinality({q \in Proc : lastArrived[q] = gen})

(* No process is more than one instance ahead of another. *)
PhaseInv ==
  /\ \A p \in Proc : myPhase[p] \in {gen - 1, gen}
  /\ \A p, q \in Proc : myPhase[p] - myPhase[q] \in {-1, 0, 1}

ArrivedInv ==
  /\ \A q \in arrived : /\ myPhase[q] = gen
                        /\ pc[q] = "waiting"
                        /\ lastArrived[q] = gen
  /\ \A q \in Proc : (pc[q] = "working" /\ myPhase[q] = gen) => q \notin arrived

(***************************************************************************)
(* Safety 1: No premature release.  A process released from instance k    *)
(* requires that every process has arrived at instance k.  Some processes *)
(* may already have moved on to instance k+1.                             *)
(***************************************************************************)
NoPrematureRelease ==
  \A p \in Proc :
    (pc[p] = "released" \/ (pc[p] = "waiting" /\ gen > myPhase[p]))
      => \A q \in Proc : lastArrived[q] >= myPhase[p]

(* The same property, stated on the release transition itself. *)
NoPrematureReleaseStep ==
  [][\A p \in Proc :
       (pc[p] = "waiting" /\ pc'[p] = "released")
         => \A q \in Proc : lastArrived[q] >= myPhase[p]]_vars

(***************************************************************************)
(* Safety 2: No cross-instance mixing.  The arrival set holds only        *)
(* arrivals for the current instance.  Releases for instance k are based  *)
(* only on arrivals at k, not on arrivals at k+1 or later.                *)
(***************************************************************************)
NoCrossInstanceMixing ==
  /\ \A q \in arrived : lastArrived[q] = gen
  /\ \A p \in Proc :
       pc[p] = "released" =>
         \A q \in Proc : lastArrived[q] \in {myPhase[p], myPhase[p] + 1}
  /\ \A p \in Proc : lastArrived[p] <= myPhase[p]

(* A release step for instance k happens only after instance k completed. *)
ReleaseMatchesInstance ==
  [][\A p \in Proc :
       (pc[p] = "waiting" /\ pc'[p] = "released") => gen = myPhase[p] + 1]_vars

SafetyInv ==
  /\ TypeOK
  /\ CountInv
  /\ PhaseInv
  /\ ArrivedInv
  /\ NoPrematureRelease
  /\ NoCrossInstanceMixing

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)

(* Every process that enters the barrier is eventually released. *)
EventualRelease ==
  \A p \in Proc : (pc[p] = "waiting") ~> (pc[p] = "released")

(* No deadlock or starvation: every barrier instance eventually completes. *)
InstanceCompletes ==
  \A k \in Nat : (gen = k) ~> (gen = k + 1)

(* Eventual reuse: after release from instance k, a process later        *)
(* enters and is released from instance k+1.                             *)
EventualReuse ==
  \A p \in Proc : \A k \in Nat :
    (pc[p] = "released" /\ myPhase[p] = k)
      ~> (pc[p] = "released" /\ myPhase[p] = k + 1)

(* Each process passes the barrier infinitely often. *)
InfinitelyOftenReleased ==
  \A p \in Proc : []<>(pc[p] = "released")

-----------------------------------------------------------------------------
(* Optional state constraint for finite model checking (not part of Spec). *)
CONSTANT MaxPhase
PhaseBound == gen <= MaxPhase

THEOREM Spec => []SafetyInv
THEOREM Spec => NoPrematureReleaseStep /\ ReleaseMatchesInstance
THEOREM Spec => EventualRelease /\ InstanceCompletes /\ EventualReuse
                /\ InfinitelyOftenReleased
=============================================================================