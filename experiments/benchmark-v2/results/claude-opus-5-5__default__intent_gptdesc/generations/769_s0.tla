---------------------------- MODULE DisruptorRingBuffer ----------------------------
(***************************************************************************)
(* Abstract model of a single-producer, multi-consumer (multicast) ring    *)
(* buffer in the style of the LMAX Disruptor.                              *)
(*                                                                         *)
(*  - One producer publishes events with consecutive sequence numbers      *)
(*    0, 1, 2, ... MaxPublish-1. The payload of event s is s itself, so    *)
(*    the stored value identifies the event.                               *)
(*  - Sequence s is stored in slot s % Size of a fixed-size circular       *)
(*    buffer.                                                              *)
(*  - Publishing has two atomic steps. BeginWrite claims the slot and      *)
(*    makes it "writing", which means not yet visible and possibly         *)
(*    incomplete. EndWrite completes the write and advances the global     *)
(*    published cursor.                                                    *)
(*  - Consuming also has two atomic steps. BeginRead starts reading the    *)
(*    next slot. EndRead finishes, observes the slot value and advances    *)
(*    the consumer's private read cursor.                                  *)
(*  - The two-phase steps make it possible to state "no concurrent         *)
(*    read/write of the same slot" (no data races) as an invariant.        *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS
    Consumers,      \* set of consumer identifiers
    Size,           \* ring buffer capacity (number of slots)
    MaxPublish      \* bound on number of events published (for model checking)

ASSUME ConstAssumptions ==
    /\ Consumers # {}
    /\ Size \in Nat \ {0}
    /\ MaxPublish \in Nat

VARIABLES
    cursor,     \* global published cursor: number of events fully published
                \* (next sequence the producer will write is `cursor`)
    pstate,     \* producer phase: "idle" | "writing"
    buffer,     \* slot index -> [seq |-> sequence stored, state |-> occupancy]
    next,       \* consumer -> next sequence it will read (its read cursor)
    rstate,     \* consumer -> "idle" | "reading"
    got         \* consumer -> sequence of values observed so far (history)

vars == <<cursor, pstate, buffer, next, rstate, got>>

Slots      == 0 .. (Size - 1)
SeqNums    == 0 .. (MaxPublish - 1)
SlotStates == {"empty", "writing", "published"}

Slot(s) == s % Size

\* Sequence number of the slowest consumer (oldest unread slot), the gating sequence
MinNext == CHOOSE m \in {next[c] : c \in Consumers} :
               \A c \in Consumers : m <= next[c]

\* The producer may claim slot `cursor` only if the event previously held in
\* that slot (sequence cursor - Size) has been read by every consumer.
HasCapacity == \A c \in Consumers : cursor - next[c] < Size

\* Condition under which the producer is prevented from publishing because
\* at least one consumer lags a full buffer behind.
ProducerBlocked ==
    /\ pstate = "idle"
    /\ cursor < MaxPublish
    /\ ~HasCapacity

-----------------------------------------------------------------------------
TypeOK ==
    /\ cursor \in 0 .. MaxPublish
    /\ pstate \in {"idle", "writing"}
    /\ buffer \in [Slots -> [seq : -1 .. (MaxPublish - 1), state : SlotStates]]
    /\ next \in [Consumers -> 0 .. MaxPublish]
    /\ rstate \in [Consumers -> {"idle", "reading"}]
    /\ got \in [Consumers -> Seq(SeqNums)]

Init ==
    /\ cursor = 0
    /\ pstate = "idle"
    /\ buffer = [i \in Slots |-> [seq |-> -1, state |-> "empty"]]
    /\ next   = [c \in Consumers |-> 0]
    /\ rstate = [c \in Consumers |-> "idle"]
    /\ got    = [c \in Consumers |-> << >>]

-----------------------------------------------------------------------------
(* Producer actions *)

\* Claim the next sequence slot and begin writing it. The guard enforces the
\* capacity constraint, so the slot is never overwritten while unread.
BeginWrite ==
    /\ pstate = "idle"
    /\ cursor < MaxPublish
    /\ HasCapacity
    /\ pstate' = "writing"
    /\ buffer' = [buffer EXCEPT ![Slot(cursor)] =
                      [seq |-> cursor, state |-> "writing"]]
    /\ UNCHANGED <<cursor, next, rstate, got>>

\* Complete the write and publish: the slot becomes visible and the global
\* published cursor advances.
EndWrite ==
    /\ pstate = "writing"
    /\ buffer' = [buffer EXCEPT ![Slot(cursor)] =
                      [seq |-> cursor, state |-> "published"]]
    /\ cursor' = cursor + 1
    /\ pstate' = "idle"
    /\ UNCHANGED <<next, rstate, got>>

Producer == BeginWrite \/ EndWrite

-----------------------------------------------------------------------------
(* Consumer actions *)

\* A consumer may begin reading its next sequence only once it is published.
BeginRead(c) ==
    /\ rstate[c] = "idle"
    /\ next[c] < cursor
    /\ rstate' = [rstate EXCEPT ![c] = "reading"]
    /\ UNCHANGED <<cursor, pstate, buffer, next, got>>

\* Finish reading: observe the slot contents and advance the private cursor.
EndRead(c) ==
    /\ rstate[c] = "reading"
    /\ got'    = [got EXCEPT ![c] = Append(@, buffer[Slot(next[c])].seq)]
    /\ next'   = [next EXCEPT ![c] = @ + 1]
    /\ rstate' = [rstate EXCEPT ![c] = "idle"]
    /\ UNCHANGED <<cursor, pstate, buffer>>

Consumer(c) == BeginRead(c) \/ EndRead(c)

-----------------------------------------------------------------------------
(* Termination: all events published and read by every consumer. *)
Done ==
    /\ cursor = MaxPublish
    /\ pstate = "idle"
    /\ \A c \in Consumers : next[c] = MaxPublish /\ rstate[c] = "idle"

Terminating == Done /\ UNCHANGED vars

Next ==
    \/ Producer
    \/ \E c \in Consumers : Consumer(c)
    \/ Terminating

\* Fairness: continuously enabled producer and consumer steps are not ignored
\* forever. Each step stays enabled until taken, because consumers only
\* advance and the producer only advances. So weak fairness is enough to
\* guarantee eventual reads.
Fairness ==
    /\ WF_vars(Producer)
    /\ \A c \in Consumers : WF_vars(Consumer(c))

Spec == Init /\ [][Next]_vars /\ Fairness

\* An alternative with strong fairness, for environments where steps may be
\* enabled only intermittently.
StrongFairness ==
    /\ SF_vars(Producer)
    /\ \A c \in Consumers : SF_vars(Consumer(c))

StrongSpec == Init /\ [][Next]_vars /\ StrongFairness

-----------------------------------------------------------------------------
(* SAFETY *)

\* No data race: a consumer never reads a slot the producer is writing.
NoDataRace ==
    \A c \in Consumers :
        (rstate[c] = "reading" /\ pstate = "writing")
            => Slot(next[c]) # Slot(cursor)

\* A reading consumer always sees a complete, published copy of exactly the
\* sequence it expects. The slot was neither overwritten nor partially written.
ReadsComplete ==
    \A c \in Consumers :
        rstate[c] = "reading" =>
            /\ next[c] < cursor
            /\ buffer[Slot(next[c])].state = "published"
            /\ buffer[Slot(next[c])].seq = next[c]

\* No overwrite: every published but not yet consumed event (for any
\* consumer) is still intact in its slot.
NoOverwrite ==
    \A c \in Consumers :
        \A s \in next[c] .. (cursor - 1) :
            /\ buffer[Slot(s)].seq = s
            /\ buffer[Slot(s)].state = "published"

\* Consumers never run ahead of the published cursor.
ConsumerBehindCursor ==
    \A c \in Consumers : next[c] <= cursor

\* Capacity constraint: the producer never gets more than Size ahead of the
\* slowest consumer. The in-flight write counts as occupying a slot.
CapacityRespected ==
    \A c \in Consumers :
        cursor - next[c] + (IF pstate = "writing" THEN 1 ELSE 0) <= Size

\* If the producer is blocked by lagging consumers, some consumer can make
\* progress, so the system never deadlocks.
BlockedImpliesConsumerCanProgress ==
    ProducerBlocked => \E c \in Consumers : next[c] < cursor

\* Each consumer only observes published sequence numbers, in strictly
\* increasing order.
MonotonicObservation ==
    \A c \in Consumers :
        /\ \A i \in 1 .. Len(got[c]) : got[c][i] < cursor
        /\ \A i \in 1 .. (Len(got[c]) - 1) : got[c][i] < got[c][i + 1]

-----------------------------------------------------------------------------
(* CONSISTENCY *)

\* Each consumer has seen exactly the published values 0 .. next[c]-1, in
\* order, with no gaps and no duplicates.
ExactInOrderDelivery ==
    \A c \in Consumers :
        /\ Len(got[c]) = next[c]
        /\ \A i \in 1 .. Len(got[c]) : got[c][i] = i - 1

SafetyInvariant ==
    /\ TypeOK
    /\ NoDataRace
    /\ ReadsComplete
    /\ NoOverwrite
    /\ ConsumerBehindCursor
    /\ CapacityRespected
    /\ BlockedImpliesConsumerCanProgress
    /\ MonotonicObservation
    /\ ExactInOrderDelivery

\* Action properties: the published cursor and the read cursors never move
\* backwards, and each advances by at most one per step.
CursorsMonotonic ==
    [][ /\ cursor' \in {cursor, cursor + 1}
        /\ \A c \in Consumers : next'[c] \in {next[c], next[c] + 1} ]_vars

\* Histories only grow by appending.
HistoryAppendOnly ==
    [][ \A c \in Consumers :
          /\ Len(got'[c]) >= Len(got[c])
          /\ SubSeq(got'[c], 1, Len(got[c])) = got[c] ]_vars

-----------------------------------------------------------------------------
(* LIVENESS *)

\* Every published event is eventually read by every consumer.
EveryPublishedEventuallyRead ==
    \A c \in Consumers : \A s \in SeqNums :
        (cursor > s) ~> (next[c] > s)

\* A consumer with published but unread events eventually makes progress.
ConsumerProgress ==
    \A c \in Consumers : \A s \in SeqNums :
        (next[c] = s /\ s < cursor) ~> (next[c] > s)

\* A blocked producer is eventually unblocked or finishes.
ProducerEventuallyUnblocked ==
    ProducerBlocked ~> (HasCapacity \/ cursor = MaxPublish)

\* All MaxPublish events are eventually published.
AllEventuallyPublished == <>(cursor = MaxPublish)

\* Eventually every consumer has read every event, and this stays true.
AllEventuallyConsumed ==
    <>[](\A c \in Consumers : next[c] = MaxPublish)

LivenessProperties ==
    /\ EveryPublishedEventuallyRead
    /\ ConsumerProgress
    /\ ProducerEventuallyUnblocked
    /\ AllEventuallyPublished
    /\ AllEventuallyConsumed

-----------------------------------------------------------------------------
THEOREM Spec => []SafetyInvariant
THEOREM Spec => CursorsMonotonic /\ HistoryAppendOnly
THEOREM Spec => LivenessProperties
=============================================================================