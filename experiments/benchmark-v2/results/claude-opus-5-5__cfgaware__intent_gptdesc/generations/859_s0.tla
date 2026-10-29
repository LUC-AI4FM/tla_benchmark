------------------------------ MODULE ReadersWriters ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT NumActors

\* Default model value for the number of actors; the configuration may
\* substitute it for NumActors (e.g. NumActors <- n).
n == 3

ASSUME NumActors \in Nat \ {0}

Actors == 1..NumActors

VARIABLES
    readers,          \* set of actors currently reading (in critical section)
    writers,          \* set of actors currently writing (in critical section)
    waitingReaders,   \* set of actors waiting to read
    waitingWriters    \* set of actors waiting to write

vars == <<readers, writers, waitingReaders, waitingWriters>>

Busy == readers \cup writers \cup waitingReaders \cup waitingWriters

Idle(a) == a \notin Busy

-----------------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waitingReaders = {}
    /\ waitingWriters = {}

\* A process requests to read
TryRead(a) ==
    /\ Idle(a)
    /\ waitingReaders' = waitingReaders \cup {a}
    /\ UNCHANGED <<readers, writers, waitingWriters>>

\* A process requests to write
TryWrite(a) ==
    /\ Idle(a)
    /\ waitingWriters' = waitingWriters \cup {a}
    /\ UNCHANGED <<readers, writers, waitingReaders>>

\* A waiting reader enters: no active writer and no waiting writer
\* (writer preference, preventing writer starvation)
StartRead(a) ==
    /\ a \in waitingReaders
    /\ writers = {}
    /\ waitingWriters = {}
    /\ readers' = readers \cup {a}
    /\ waitingReaders' = waitingReaders \ {a}
    /\ UNCHANGED <<writers, waitingWriters>>

\* A waiting writer enters: exclusive access required
StartWrite(a) ==
    /\ a \in waitingWriters
    /\ readers = {}
    /\ writers = {}
    /\ writers' = {a}
    /\ waitingWriters' = waitingWriters \ {a}
    /\ UNCHANGED <<readers, waitingReaders>>

\* A reader leaves the critical section
EndRead(a) ==
    /\ a \in readers
    /\ readers' = readers \ {a}
    /\ UNCHANGED <<writers, waitingReaders, waitingWriters>>

\* A writer leaves the critical section
EndWrite(a) ==
    /\ a \in writers
    /\ writers' = writers \ {a}
    /\ UNCHANGED <<readers, waitingReaders, waitingWriters>>

Next ==
    \E a \in Actors :
        \/ TryRead(a)
        \/ TryWrite(a)
        \/ StartRead(a)
        \/ StartWrite(a)
        \/ EndRead(a)
        \/ EndWrite(a)

Fairness ==
    \A a \in Actors :
        /\ WF_vars(StartRead(a))
        /\ SF_vars(StartWrite(a))
        /\ WF_vars(EndRead(a))
        /\ WF_vars(EndWrite(a))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waitingReaders \subseteq Actors
    /\ waitingWriters \subseteq Actors
    /\ Cardinality(readers) <= NumActors
    /\ Cardinality(waitingWriters) <= NumActors

\* (1) A writer is alone in the critical section
WriterExclusive ==
    writers # {} => (readers = {} /\ Cardinality(writers) = 1)

\* (2) Readers may share the critical section only when no writer is present
ReadersShare ==
    readers # {} => writers = {}

\* (3) Bounded sets
Bounded ==
    /\ Cardinality(readers) <= NumActors
    /\ Cardinality(waitingWriters) <= NumActors

\* Each process plays at most one role at a time
Disjoint ==
    /\ readers \cap writers = {}
    /\ readers \cap waitingReaders = {}
    /\ readers \cap waitingWriters = {}
    /\ writers \cap waitingReaders = {}
    /\ writers \cap waitingWriters = {}
    /\ waitingReaders \cap waitingWriters = {}

Safety ==
    /\ WriterExclusive
    /\ ReadersShare
    /\ Bounded
    /\ Disjoint

-----------------------------------------------------------------------------
\* (4) Deadlock freedom between readers and writers

\* Waiting readers with no waiting writers eventually get in
\* (unless a writer arrives and takes precedence)
ReadersProgress ==
    (waitingReaders # {} /\ waitingWriters = {})
        ~> (readers # {} \/ waitingWriters # {})

\* Waiting writers eventually get in
WritersProgress ==
    (waitingWriters # {}) ~> (writers # {})

\* Every individual waiting writer eventually writes
WriterStarvationFree ==
    \A a \in Actors : (a \in waitingWriters) ~> (a \in writers)

\* Processes in the critical section eventually leave it
CriticalSectionExits ==
    \A a \in Actors :
        /\ (a \in readers) ~> (a \notin readers)
        /\ (a \in writers) ~> (a \notin writers)

Liveness ==
    /\ ReadersProgress
    /\ WritersProgress
    /\ WriterStarvationFree
    /\ CriticalSectionExits

=============================================================================