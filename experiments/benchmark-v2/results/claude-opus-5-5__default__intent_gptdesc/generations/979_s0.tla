------------------------- MODULE TwoPhaseRegister -------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Values,      \* set of values the producer may write
          InitVal      \* initial value of the register

ASSUME InitVal \in Values

NoVal == CHOOSE v : v \notin Values

VARIABLES
    reg,        \* the visible (committed) register contents
    staged,     \* the producer's privately prepared value, or NoVal
    pstate,     \* producer phase: "idle" or "prepared"
    committed,  \* set of all values that have ever been committed
    cstate,     \* consumer phase: "idle" or "reading"
    lastRead    \* value returned by the consumer's most recent read

vars == <<reg, staged, pstate, committed, cstate, lastRead>>

---------------------------------------------------------------------------
TypeOK ==
    /\ reg \in Values
    /\ staged \in Values \cup {NoVal}
    /\ pstate \in {"idle", "prepared"}
    /\ committed \subseteq Values
    /\ cstate \in {"idle", "reading"}
    /\ lastRead \in Values

Init ==
    /\ reg = InitVal
    /\ staged = NoVal
    /\ pstate = "idle"
    /\ committed = {}
    /\ cstate = "idle"
    /\ lastRead = InitVal

---------------------------------------------------------------------------
\* Producer actions

\* Prepare phase (also covers retry / re-prepare of a different value).
\* Only the private staging area changes; reg is untouched.
Prepare(v) ==
    /\ pstate \in {"idle", "prepared"}
    /\ staged' = v
    /\ pstate' = "prepared"
    /\ UNCHANGED <<reg, committed, cstate, lastRead>>

\* Abandon a prepared update (retry later).
Abort ==
    /\ pstate = "prepared"
    /\ staged' = NoVal
    /\ pstate' = "idle"
    /\ UNCHANGED <<reg, committed, cstate, lastRead>>

\* Commit phase: atomically publish the prepared value.
Commit ==
    /\ pstate = "prepared"
    /\ staged \in Values
    /\ reg' = staged
    /\ committed' = committed \cup {staged}
    /\ staged' = NoVal
    /\ pstate' = "idle"
    /\ UNCHANGED <<cstate, lastRead>>

Producer == (\E v \in Values : Prepare(v)) \/ Abort \/ Commit

---------------------------------------------------------------------------
\* Consumer actions (asynchronous, may interleave with any producer step)

BeginRead ==
    /\ cstate = "idle"
    /\ cstate' = "reading"
    /\ UNCHANGED <<reg, staged, pstate, committed, lastRead>>

\* The read takes effect atomically on the visible register.
EndRead ==
    /\ cstate = "reading"
    /\ lastRead' = reg
    /\ cstate' = "idle"
    /\ UNCHANGED <<reg, staged, pstate, committed>>

Consumer == BeginRead \/ EndRead

---------------------------------------------------------------------------
Next == Producer \/ Consumer

Fairness ==
    /\ SF_vars(Commit)
    /\ WF_vars(BeginRead)
    /\ WF_vars(EndRead)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
\* SAFETY

\* (1) Reads return either the initial value or a fully committed value.
ReadsValid == lastRead \in committed \cup {InitVal}

\* The visible register only ever holds the initial value or a committed one.
RegisterValid == reg \in committed \cup {InitVal}

\* Atomic visibility: a prepared value that was never committed is
\* never visible and never read.
NoPartialVisibility ==
    (pstate = "prepared" /\ staged \notin committed \cup {InitVal})
        => /\ reg # staged
           /\ lastRead # staged

\* Consistency of producer phase and staging area.
PhaseConsistent == (pstate = "idle") <=> (staged = NoVal)

\* (2) The prepare phase never changes the visible register.
PrepareInvisible ==
    [][\A v \in Values : Prepare(v) => reg' = reg]_vars

\* Only a commit can change the visible value, and it installs the staged value.
OnlyCommitChangesReg ==
    [][(reg' # reg) => (pstate = "prepared" /\ reg' = staged /\ pstate' = "idle")]_vars

\* (3) A committed value remains visible until overwritten by a later commit:
\* reg is never changed except by a commit, and committed values are never lost.
CommittedPersists ==
    [][ /\ (reg' # reg) => Commit
        /\ committed \subseteq committed' ]_vars

\* Each read returns exactly the currently visible (latest committed) value.
ReadSeesCurrent == [][EndRead => lastRead' = reg]_vars

\* The consumer is never blocked: some consumer step is always enabled.
ConsumerNeverBlocked == ENABLED BeginRead \/ ENABLED EndRead

---------------------------------------------------------------------------
\* LIVENESS

\* If the producer keeps reaching the prepared state (keeps trying to
\* commit), then commits eventually happen.
CommitProgress ==
    ([]<>(pstate = "prepared")) => []<><<Commit>>_vars

\* A producer that stays prepared eventually commits.
PreparedEventuallyCommits ==
    (pstate = "prepared") ~> (pstate = "idle")

\* The consumer is never blocked indefinitely: each read completes and
\* the consumer reads infinitely often.
ReadCompletes == (cstate = "reading") ~> (cstate = "idle")

ConsumerProgress == []<><<EndRead>>_vars

---------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ ReadsValid /\ RegisterValid
                   /\ NoPartialVisibility /\ PhaseConsistent
                   /\ ConsumerNeverBlocked)
THEOREM Spec => PrepareInvisible /\ OnlyCommitChangesReg
                /\ CommittedPersists /\ ReadSeesCurrent
THEOREM Spec => CommitProgress /\ ReadCompletes /\ ConsumerProgress
=============================================================================