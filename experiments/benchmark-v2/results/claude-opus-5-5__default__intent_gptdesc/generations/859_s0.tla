---------------------------- MODULE ReadersWriters ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Procs == 1..N

VARIABLES
    readers,          \* processes currently reading in the critical section
    writers,          \* processes currently writing in the critical section
    waitingReaders,   \* processes queued, waiting to read
    waitingWriters,   \* processes queued, waiting to write
    turn              \* arbitration flag to prevent starvation: "read" or "write"

vars == <<readers, writers, waitingReaders, waitingWriters, turn>>

Busy == readers \cup writers \cup waitingReaders \cup waitingWriters

Idle == Procs \ Busy

-----------------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq Procs
    /\ writers \subseteq Procs
    /\ waitingReaders \subseteq Procs
    /\ waitingWriters \subseteq Procs
    /\ turn \in {"read", "write"}
    \* each process plays at most one role at any time
    /\ readers \cap writers = {}
    /\ readers \cap waitingReaders = {}
    /\ readers \cap waitingWriters = {}
    /\ writers \cap waitingReaders = {}
    /\ writers \cap waitingWriters = {}
    /\ waitingReaders \cap waitingWriters = {}

-----------------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waitingReaders = {}
    /\ waitingWriters = {}
    /\ turn = "read"

\* An idle process asks to read: it is queued in the reader waiting set.
RequestRead(p) ==
    /\ p \in Idle
    /\ waitingReaders' = waitingReaders \cup {p}
    /\ UNCHANGED <<readers, writers, waitingWriters, turn>>

\* An idle process asks to write: it is queued in the writer waiting set.
RequestWrite(p) ==
    /\ p \in Idle
    /\ waitingWriters' = waitingWriters \cup {p}
    /\ UNCHANGED <<readers, writers, waitingReaders, turn>>

\* A waiting reader enters, provided no writer is active and either no
\* writer is waiting or it is the readers' turn. Afterwards the turn is
\* handed to writers so that waiting writers cannot be starved.
StartRead(p) ==
    /\ p \in waitingReaders
    /\ writers = {}
    /\ (waitingWriters = {} \/ turn = "read")
    /\ readers' = readers \cup {p}
    /\ waitingReaders' = waitingReaders \ {p}
    /\ turn' = "write"
    /\ UNCHANGED <<writers, waitingWriters>>

\* A reader leaves the critical section.
EndRead(p) ==
    /\ p \in readers
    /\ readers' = readers \ {p}
    /\ UNCHANGED <<writers, waitingReaders, waitingWriters, turn>>

\* A waiting writer enters, provided the critical section is empty and
\* either no reader is waiting or it is the writers' turn.
StartWrite(p) ==
    /\ p \in waitingWriters
    /\ readers = {}
    /\ writers = {}
    /\ (waitingReaders = {} \/ turn = "write")
    /\ writers' = {p}
    /\ waitingWriters' = waitingWriters \ {p}
    /\ UNCHANGED <<readers, waitingReaders, turn>>

\* A writer leaves; the turn is handed to readers.
EndWrite(p) ==
    /\ p \in writers
    /\ writers' = writers \ {p}
    /\ turn' = "read"
    /\ UNCHANGED <<readers, waitingReaders, waitingWriters>>

Next ==
    \E p \in Procs :
        \/ RequestRead(p)
        \/ RequestWrite(p)
        \/ StartRead(p)
        \/ EndRead(p)
        \/ StartWrite(p)
        \/ EndWrite(p)

Fairness ==
    \A p \in Procs :
        /\ SF_vars(StartRead(p))
        /\ SF_vars(StartWrite(p))
        /\ WF_vars(EndRead(p))
        /\ WF_vars(EndWrite(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

\* (1) A writer in the critical section excludes every other reader or writer.
WriterExclusion ==
    writers # {} => (Cardinality(writers) = 1 /\ readers = {})

\* (2) Readers may share the critical section, but only with no writer present.
ReadersShareOnlyWithoutWriter ==
    readers # {} => writers = {}

\* Combined mutual-exclusion statement.
MutualExclusion ==
    \A p, q \in readers \cup writers :
        (p # q) => (p \in readers /\ q \in readers)

\* (3) The active reader set and the writer waiting set are bounded by N.
Bounded ==
    /\ Cardinality(readers) <= N
    /\ Cardinality(waitingWriters) <= N
    /\ Cardinality(waitingReaders) <= N
    /\ Cardinality(writers) <= 1

\* (4) Absence of deadlock: if someone is waiting, then either the critical
\* section is occupied (and will be released) or some waiting process can enter.
NoDeadlock ==
    (waitingReaders # {} \/ waitingWriters # {}) =>
        \/ readers # {}
        \/ writers # {}
        \/ ENABLED (\E p \in Procs : StartRead(p) \/ StartWrite(p))

Safety ==
    /\ TypeOK
    /\ WriterExclusion
    /\ ReadersShareOnlyWithoutWriter
    /\ MutualExclusion
    /\ Bounded
    /\ NoDeadlock

THEOREM Spec => []Safety

-----------------------------------------------------------------------------
\* Liveness properties

\* (4a) Waiting readers with no waiting writers: readers eventually enter.
ReadersProgress ==
    (waitingReaders # {} /\ waitingWriters = {}) ~> (readers # {})

\* (4b) Waiting writers with no waiting readers: writers eventually enter.
WritersProgress ==
    (waitingWriters # {} /\ waitingReaders = {}) ~> (writers # {})

\* Starvation freedom for each individual request under fair scheduling.
ReaderStarvationFree ==
    \A p \in Procs : (p \in waitingReaders) ~> (p \in readers)

WriterStarvationFree ==
    \A p \in Procs : (p \in waitingWriters) ~> (p \in writers)

\* Every process eventually leaves the critical section.
ReadersLeave ==
    \A p \in Procs : (p \in readers) ~> (p \notin readers)

WritersLeave ==
    \A p \in Procs : (p \in writers) ~> (p \notin writers)

Liveness ==
    /\ ReadersProgress
    /\ WritersProgress
    /\ ReaderStarvationFree
    /\ WriterStarvationFree
    /\ ReadersLeave
    /\ WritersLeave

THEOREM Spec => Liveness

=============================================================================