---------------------------- MODULE SyncTerminationDetection ----------------------------
(***************************************************************************)
(* Synchronous distributed termination detection.                          *)
(*                                                                         *)
(* N processes run in lock-step synchronous rounds. Each round has three   *)
(* phases:                                                                 *)
(*                                                                         *)
(*   1. "compute": every process takes one local step at the same time.    *)
(*      An active process may send work messages to any set of processes   *)
(*      and may then stay active or become passive. A passive process does *)
(*      nothing.                                                           *)
(*   2. "deliver": every message sent this round is delivered reliably in  *)
(*      the same round. A process that receives a message consumes it and  *)
(*      becomes active.                                                    *)
(*   3. "detect": a coordinator runs a synchronous convergecast. It        *)
(*      collects each process's local report: its activity status and its  *)
(*      colour. A process is black if it sent or received a message this   *)
(*      round. The coordinator sets the global termination flag if every   *)
(*      report says "passive and white". It uses only the local reports,   *)
(*      not any external oracle.                                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Procs  == 1..N
Phases == {"compute", "deliver", "detect"}
Colors == {"white", "black"}

VARIABLES
    active,      \* active[p] = TRUE iff process p is active
    inbox,       \* inbox[q]  = set of senders whose message to q is in transit
    color,       \* local communication colour reported to the detector
    phase,       \* current phase of the synchronous round
    terminated   \* global termination flag

vars == <<active, inbox, color, phase, terminated>>

----------------------------------------------------------------------------
TypeOK ==
    /\ active     \in [Procs -> BOOLEAN]
    /\ inbox      \in [Procs -> SUBSET Procs]
    /\ color      \in [Procs -> Colors]
    /\ phase      \in Phases
    /\ terminated \in BOOLEAN

\* True global quiescence: every process is passive and no message is in transit.
AllPassive == \A p \in Procs : ~active[p]
NoMessages == \A p \in Procs : inbox[p] = {}
Quiescent  == AllPassive /\ NoMessages

\* What the coordinator can compute from the local reports alone.
ReportsSayDone == \A p \in Procs : ~active[p] /\ color[p] = "white"

----------------------------------------------------------------------------
\* The initial active set is an arbitrary subset of the processes.
Init ==
    /\ active     \in [Procs -> BOOLEAN]
    /\ inbox      = [p \in Procs |-> {}]
    /\ color      = [p \in Procs |-> "white"]
    /\ phase      = "compute"
    /\ terminated = FALSE

\* Phase 1: all processes take one local step simultaneously.
\* The choices of which messages to send and whether to stay active are nondeterministic.
Compute ==
    /\ phase = "compute"
    /\ \E sendTo \in [Procs -> SUBSET Procs], stay \in [Procs -> BOOLEAN] :
         /\ \A p \in Procs : ~active[p] => (sendTo[p] = {} /\ stay[p] = FALSE)
         /\ active' = [p \in Procs |-> active[p] /\ stay[p]]
         /\ inbox'  = [q \in Procs |-> {p \in Procs : q \in sendTo[p]}]
         /\ color'  = [p \in Procs |-> IF sendTo[p] # {} THEN "black" ELSE "white"]
    /\ phase' = "deliver"
    /\ UNCHANGED terminated

\* Phase 2: reliable delivery within the same round.
\* Receivers consume their messages and become active.
Deliver ==
    /\ phase = "deliver"
    /\ active' = [p \in Procs |-> active[p] \/ inbox[p] # {}]
    /\ color'  = [p \in Procs |-> IF inbox[p] # {} THEN "black" ELSE color[p]]
    /\ inbox'  = [p \in Procs |-> {}]
    /\ phase'  = "detect"
    /\ UNCHANGED terminated

\* Phase 3: the coordinator collects the reports and decides.
\* The flag is never reset.
Detect ==
    /\ phase = "detect"
    /\ terminated' = (terminated \/ ReportsSayDone)
    /\ phase' = "compute"
    /\ UNCHANGED <<active, inbox, color>>

Next == Compute \/ Deliver \/ Detect

\* Fairness: the synchronous rounds keep advancing, so every phase eventually runs.
Fairness ==
    /\ WF_vars(Compute)
    /\ WF_vars(Deliver)
    /\ WF_vars(Detect)

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)

\* Main safety property: the flag is set only in globally quiescent states.
TerminationSafety == terminated => Quiescent

\* Supporting invariant: messages are in transit only between compute and deliver.
InboxInv == phase # "deliver" => NoMessages

\* Supporting invariant: in the detect phase, a black process implies
\* that some process is active (it is the receiver or the sender's target).
ColorInv ==
    (phase = "detect" /\ \E p \in Procs : color[p] = "black")
        => \E q \in Procs : active[q]

\* Supporting invariant: in the detect phase, the reports are accurate.
DetectSound == phase = "detect" => (ReportsSayDone <=> AllPassive)

\* Supporting invariant: once the flag is set, every process stays passive.
TerminatedPassive == terminated => AllPassive

Invariants ==
    /\ TypeOK
    /\ TerminationSafety
    /\ InboxInv
    /\ ColorInv
    /\ DetectSound
    /\ TerminatedPassive

(***************************************************************************)
(* Temporal properties                                                     *)
(***************************************************************************)

\* No false resets: once the flag is set, it stays set.
NoFalseReset == [][terminated => terminated']_vars

\* Quiescence is stable: a passive system with no messages stays that way.
QuiescenceStable == [][Quiescent => Quiescent']_vars

\* Liveness: quiescence is detected within a bounded number of rounds.
\* At most one full round of three phase steps is needed.
TerminationLiveness == Quiescent ~> terminated

\* Progress / non-false-detection: while any process is active or any
\* message is in transit, the flag is not set. This follows from
\* TerminationSafety. Runs in which processes keep generating work are
\* allowed by Compute, and in those runs the flag is never set.
NoFalseDetection == [](~Quiescent => ~terminated)

THEOREM Spec => []Invariants
THEOREM Spec => NoFalseReset /\ QuiescenceStable /\ NoFalseDetection
THEOREM Spec => TerminationLiveness
=============================================================================