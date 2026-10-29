---------------------------- MODULE TwoPhaseRegister ----------------------------
EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* A single shared register written by a producer using a two-phase       *)
(* protocol (prepare, then commit) and read by a consumer at any time.    *)
(* Prepared (staged) values stay private to the producer until a commit   *)
(* makes them visible atomically. The producer may re-prepare or abort    *)
(* before committing.                                                     *)
(***************************************************************************)

Values  == {1, 2}          \* values the producer may write
InitVal == 0               \* initial register value
None    == 0 - 1           \* marker for "no staged value"

AllVals == Values \cup {InitVal}

VARIABLES
    reg,            \* the visible shared register
    staged,         \* producer's privately prepared value (or None)
    pphase,         \* producer phase: "idle" or "prepared"
    committed,      \* set of all values ever committed (plus the initial value)
    lastCommitted,  \* most recently committed value (InitVal initially)
    readVal,        \* value most recently observed by the consumer
    rtoggle         \* flips on each read, so every read is a real step

vars == <<reg, staged, pphase, committed, lastCommitted, readVal, rtoggle>>

TypeOK ==
    /\ reg \in AllVals
    /\ staged \in Values \cup {None}
    /\ pphase \in {"idle", "prepared"}
    /\ committed \subseteq AllVals
    /\ lastCommitted \in AllVals
    /\ readVal \in AllVals
    /\ rtoggle \in BOOLEAN

Init ==
    /\ reg = InitVal
    /\ staged = None
    /\ pphase = "idle"
    /\ committed = {InitVal}
    /\ lastCommitted = InitVal
    /\ readVal = InitVal
    /\ rtoggle = FALSE

(* Phase 1: the producer prepares a value. This is allowed in the idle      *)
(* phase, or again from the prepared phase (a retry or re-prepare). It does *)
(* not touch the visible register.                                          *)
Prepare(v) ==
    /\ staged' = v
    /\ pphase' = "prepared"
    /\ UNCHANGED <<reg, committed, lastCommitted, readVal, rtoggle>>

(* The producer abandons a prepared update. *)
Abort ==
    /\ pphase = "prepared"
    /\ staged' = None
    /\ pphase' = "idle"
    /\ UNCHANGED <<reg, committed, lastCommitted, readVal, rtoggle>>

(* Phase 2: the producer atomically publishes the prepared value. *)
Commit ==
    /\ pphase = "prepared"
    /\ staged # None
    /\ reg' = staged
    /\ committed' = committed \cup {staged}
    /\ lastCommitted' = staged
    /\ staged' = None
    /\ pphase' = "idle"
    /\ UNCHANGED <<readVal, rtoggle>>

(* The consumer reads the visible register. It is always enabled and never blocks. *)
Read ==
    /\ readVal' = reg
    /\ rtoggle' = ~rtoggle
    /\ UNCHANGED <<reg, staged, pphase, committed, lastCommitted>>

ProducerStep == (\E v \in Values : Prepare(v)) \/ Abort \/ Commit

Next == ProducerStep \/ Read

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ SF_vars(Commit)
    /\ WF_vars(Read)

-----------------------------------------------------------------------------
(* Safety *)

(* (1) Reads return the initial value or some fully committed value. *)
ReadsCommitted == readVal \in committed

(* (2) A prepare does not expose new values. The visible register always   *)
(*     holds a committed value, namely the latest commit, and never a value *)
(*     that is only staged.                                                 *)
NoPartialVisibility ==
    /\ reg \in committed
    /\ (pphase = "prepared" /\ staged \notin committed) => reg # staged

(* (3) The visible register is the most recently committed value. *)
CommittedVisible == reg = lastCommitted

PhaseConsistent == (pphase = "idle") <=> (staged = None)

Inv ==
    /\ TypeOK
    /\ ReadsCommitted
    /\ NoPartialVisibility
    /\ CommittedVisible
    /\ PhaseConsistent

(* Action-level safety: only a commit changes the register, and it installs the staged value. *)
OnlyCommitChangesReg ==
    [][reg' # reg => (pphase = "prepared" /\ reg' = staged)]_vars

(* A committed value stays visible until a later commit overwrites it. *)
CommitPersists ==
    [][(reg' # reg) => (lastCommitted' = reg' /\ reg' \in committed')]_vars

-----------------------------------------------------------------------------
(* Liveness *)

(* If the producer keeps attempting to commit, some commit eventually happens. *)
CommitProgress ==
    []<>(pphase = "prepared") => []<><<Commit>>_vars

(* A prepared update is eventually resolved: it is committed or abandoned. *)
PreparedResolved ==
    (pphase = "prepared") ~> (pphase = "idle")
        \/ []<>(pphase = "prepared")

(* The consumer is never blocked indefinitely. *)
ConsumerNotBlocked == []<><<Read>>_vars

Liveness == CommitProgress /\ ConsumerNotBlocked

THEOREM Spec => []Inv
THEOREM Spec => OnlyCommitChangesReg /\ CommitPersists
THEOREM Spec => Liveness
=============================================================================