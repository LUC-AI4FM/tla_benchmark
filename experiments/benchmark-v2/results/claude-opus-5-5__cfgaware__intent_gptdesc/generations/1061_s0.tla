------------------------- MODULE SyncTerminationDetection -------------------------
(***************************************************************************)
(* Synchronous distributed termination detection for N processes.          *)
(*                                                                         *)
(* Each synchronous round has three phases:                                *)
(*   "compute" : every active process may send work messages to any        *)
(*               processes and may become passive. Passive processes do    *)
(*               nothing.                                                  *)
(*   "deliver" : every in-transit message is delivered reliably within     *)
(*               the round. A receiver becomes active. Each process then   *)
(*               sends a status report (passive or not) on a control       *)
(*               channel to the detector.                                  *)
(*   "detect"  : the detector combines the reports. It sets the global     *)
(*               termination flag iff all processes reported passive.      *)
(*               It uses no external oracle, only the reports it receives. *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 1

Procs  == 1..N
Phases == {"compute", "deliver", "detect"}

VARIABLES
    active,      \* active[p] : TRUE iff process p is active
    msgs,        \* msgs[p]   : number of work messages in transit to p
    report,      \* report[p] : last status report of p (TRUE = passive)
    phase,       \* current phase of the synchronous round
    terminated   \* global termination flag

vars == <<active, msgs, report, phase, terminated>>

-----------------------------------------------------------------------------

TypeOK ==
    /\ active     \in [Procs -> BOOLEAN]
    /\ msgs       \in [Procs -> 0..N]
    /\ report     \in [Procs -> BOOLEAN]
    /\ phase      \in Phases
    /\ terminated \in BOOLEAN

AllPassive == \A p \in Procs : ~active[p]
NoMsgs     == \A p \in Procs : msgs[p] = 0
Quiescent  == AllPassive /\ NoMsgs

-----------------------------------------------------------------------------

(* The initial state has an arbitrary subset of processes active. *)
Init ==
    /\ active     \in [Procs -> BOOLEAN]
    /\ msgs       = [p \in Procs |-> 0]
    /\ report     = [p \in Procs |-> FALSE]
    /\ phase      = "compute"
    /\ terminated = FALSE

(* Synchronous local computation. All processes act at the same time.     *)
(* An active process may send messages to any set of destinations. It may *)
(* stay active or become passive. A passive process does nothing.         *)
Compute ==
    /\ phase = "compute"
    /\ \E newAct \in [Procs -> BOOLEAN], dests \in [Procs -> SUBSET Procs] :
          /\ \A p \in Procs : ~active[p] => (newAct[p] = FALSE /\ dests[p] = {})
          /\ active' = newAct
          /\ msgs'   = [q \in Procs |->
                          Cardinality({p \in Procs : q \in dests[p]})]
    /\ phase' = "deliver"
    /\ UNCHANGED <<report, terminated>>

(* Reliable delivery within the same round. A receiver becomes active.    *)
(* Each process then reports its status to the detector.                  *)
Deliver ==
    /\ phase = "deliver"
    /\ active' = [q \in Procs |-> active[q] \/ msgs[q] > 0]
    /\ msgs'   = [q \in Procs |-> 0]
    /\ report' = [q \in Procs |-> ~(active[q] \/ msgs[q] > 0)]
    /\ phase'  = "detect"
    /\ UNCHANGED terminated

(* The detector combines the reports. The flag is never cleared. *)
Detect ==
    /\ phase = "detect"
    /\ terminated' = (terminated \/ \A p \in Procs : report[p])
    /\ phase' = "compute"
    /\ UNCHANGED <<active, msgs, report>>

Next == Compute \/ Deliver \/ Detect

(* Weak fairness ensures that the synchronous rounds keep advancing. *)
Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Invariants *)

(* Safety: the flag is set only when the system is globally quiescent. *)
TDCorrect == terminated => Quiescent

(* Helper invariant: reports are accurate while the detector reads them. *)
ReportsAccurate ==
    phase = "detect" => (NoMsgs /\ \A p \in Procs : report[p] = ~active[p])

(* Messages are outstanding only between the compute and deliver phases. *)
MsgsOnlyInDeliver == phase # "deliver" => NoMsgs

Inv == TypeOK /\ TDCorrect /\ ReportsAccurate /\ MsgsOnlyInDeliver

-----------------------------------------------------------------------------
(* Temporal properties *)

(* Liveness: quiescence leads to detection within finitely many rounds. *)
Liveness == Quiescent ~> terminated

(* No false resets: once set, the flag stays set. *)
FlagStable == [][terminated => terminated']_vars

(* Quiescence is stable: once reached, it persists. *)
QuiescenceStable == [][Quiescent => Quiescent']_vars

(* Progress: while work exists, termination is not declared. *)
NoFalseDetection == [](~Quiescent => ~terminated)

THEOREM Spec => []Inv
THEOREM Spec => Liveness /\ FlagStable

=============================================================================