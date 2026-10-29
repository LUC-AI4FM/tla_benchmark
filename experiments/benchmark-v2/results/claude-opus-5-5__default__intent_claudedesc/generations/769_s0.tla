---------------------------- MODULE SPMCDisruptor ----------------------------
(***************************************************************************)
(* Single Producer, Multiple Consumer (SPMC) Disruptor ring buffer.        *)
(*                                                                         *)
(* One producer publishes sequence numbers 0, 1, 2, ... into a circular    *)
(* ring buffer of capacity Size. Each consumer reads every published event *)
(* in order (multicast). The producer may be at most Size slots ahead of   *)
(* the slowest consumer, so it never overwrites an unread slot.            *)
(*                                                                         *)
(* Each slot access has two steps, a begin step and an end step. This     *)
(* makes concurrent accesses visible to the model checker, so data races   *)
(* can be detected.                                                        *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS
    MaxPublished,   \* Bound on the number of events the producer publishes
    Size,           \* Capacity of the ring buffer
    Writer,         \* Identifier of the single producer thread
    Consumers,      \* Set of consumer thread identifiers
    NULL            \* Value of a slot that has never been written

ASSUME /\ MaxPublished \in Nat \ {0}
       /\ Size \in Nat \ {0}
       /\ Consumers # {}
       /\ Writer \notin Consumers
       /\ NULL \notin Nat

VARIABLES
    ringbuffer,     \* [slots, readers, writers] per slot index
    published,      \* Producer cursor: number of events published so far
    read,           \* read[c] = sequence number consumer c reads next
    pc,             \* Program counter per thread: "Advance" or "Access"
    consumed        \* consumed[c] = sequence of values read by consumer c

vars == <<ringbuffer, published, read, pc, consumed>>

Threads  == Consumers \cup {Writer}
Indices  == 0 .. (Size - 1)
Values   == 0 .. (MaxPublished - 1)

IndexOf(seq) == seq % Size

MinReadCursor ==
    CHOOSE m \in {read[c] : c \in Consumers} : \A c \in Consumers : m <= read[c]

-----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ ringbuffer \in [ slots   : [Indices -> Values \cup {NULL}],
                        readers : [Indices -> SUBSET Consumers],
                        writers : [Indices -> SUBSET {Writer}] ]
    /\ published \in 0 .. MaxPublished
    /\ read \in [Consumers -> 0 .. MaxPublished]
    /\ pc \in [Threads -> {"Advance", "Access"}]
    /\ consumed \in [Consumers -> Seq(Values)]

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ ringbuffer = [ slots   |-> [i \in Indices |-> NULL],
                      readers |-> [i \in Indices |-> {}],
                      writers |-> [i \in Indices |-> {}] ]
    /\ published = 0
    /\ read = [c \in Consumers |-> 0]
    /\ pc = [t \in Threads |-> "Advance"]
    /\ consumed = [c \in Consumers |-> << >>]

-----------------------------------------------------------------------------
(* Producer actions *)

\* The producer claims the next slot. It needs room, meaning it is less
\* than one full buffer ahead of the slowest consumer.
BeginWrite ==
    LET next  == published
        index == IndexOf(next)
    IN
    /\ pc[Writer] = "Advance"
    /\ next < MaxPublished
    /\ next < MinReadCursor + Size
    /\ ringbuffer' = [ringbuffer EXCEPT !.writers[index] = @ \cup {Writer}]
    /\ pc' = [pc EXCEPT ![Writer] = "Access"]
    /\ UNCHANGED <<published, read, consumed>>

\* The producer writes the sequence number into the slot, releases the
\* slot, and then publishes the slot by advancing its cursor.
EndWrite ==
    LET next  == published
        index == IndexOf(next)
    IN
    /\ pc[Writer] = "Access"
    /\ ringbuffer' = [ringbuffer EXCEPT !.slots[index]   = next,
                                        !.writers[index] = @ \ {Writer}]
    /\ published' = published + 1
    /\ pc' = [pc EXCEPT ![Writer] = "Advance"]
    /\ UNCHANGED <<read, consumed>>

-----------------------------------------------------------------------------
(* Consumer actions *)

\* Consumer c starts reading its next sequence once that sequence is published.
BeginRead(c) ==
    LET next  == read[c]
        index == IndexOf(next)
    IN
    /\ pc[c] = "Advance"
    /\ next < published
    /\ ringbuffer' = [ringbuffer EXCEPT !.readers[index] = @ \cup {c}]
    /\ pc' = [pc EXCEPT ![c] = "Access"]
    /\ UNCHANGED <<published, read, consumed>>

\* Consumer c reads the value, releases the slot, and advances its cursor.
EndRead(c) ==
    LET next  == read[c]
        index == IndexOf(next)
    IN
    /\ pc[c] = "Access"
    /\ consumed' = [consumed EXCEPT ![c] = Append(@, ringbuffer.slots[index])]
    /\ ringbuffer' = [ringbuffer EXCEPT !.readers[index] = @ \ {c}]
    /\ read' = [read EXCEPT ![c] = @ + 1]
    /\ pc' = [pc EXCEPT ![c] = "Advance"]
    /\ UNCHANGED <<published>>

-----------------------------------------------------------------------------
(* Termination: all events are published and consumed by every consumer. *)

Done ==
    /\ published = MaxPublished
    /\ \A c \in Consumers : read[c] = MaxPublished
    /\ \A t \in Threads : pc[t] = "Advance"

Terminating == Done /\ UNCHANGED vars

-----------------------------------------------------------------------------
(* Next-state relation and specification *)

Producer == BeginWrite \/ EndWrite

Consumer(c) == BeginRead(c) \/ EndRead(c)

Next ==
    \/ Producer
    \/ \E c \in Consumers : Consumer(c)
    \/ Terminating

Fairness ==
    \A c \in Consumers : WF_vars(Consumer(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* No data races. While the producer writes a slot, no consumer accesses
\* that slot, and at most one writer accesses any slot.
NoDataRaces ==
    \A i \in Indices :
        /\ Cardinality(ringbuffer.writers[i]) <= 1
        /\ (ringbuffer.writers[i] # {}) => (ringbuffer.readers[i] = {})

\* The producer is never more than one full buffer ahead of any consumer,
\* and no consumer reads past the producer cursor.
BoundedLag ==
    \A c \in Consumers :
        /\ read[c] <= published
        /\ published - read[c] <= Size

\* Every value read at position j equals the sequence number published there.
ConsumedValuesCorrect ==
    \A c \in Consumers :
        /\ Len(consumed[c]) = read[c]
        /\ \A j \in 1 .. Len(consumed[c]) : consumed[c][j] = j - 1

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Multicast. Every consumer eventually reads every published event, and
\* each value read equals the sequence number published at that position.
AllConsumersReadAllPublished ==
    \A c \in Consumers :
        \A i \in 0 .. (MaxPublished - 1) :
            (published > i) ~> (Len(consumed[c]) > i /\ consumed[c][i + 1] = i)

\* Once the producer stops publishing, every consumer has eventually read
\* the full published sequence.
EventuallyCaughtUp ==
    \A c \in Consumers :
        <>[](read[c] = published)

Liveness ==
    /\ AllConsumersReadAllPublished
    /\ EventuallyCaughtUp

THEOREM Spec => [](TypeOK /\ NoDataRaces /\ BoundedLag /\ ConsumedValuesCorrect)
THEOREM Spec => Liveness
=============================================================================