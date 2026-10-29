------------------------------ MODULE DisruptorRingBuffer ------------------------------
(***************************************************************************)
(* A bounded multi-producer / multi-consumer ring buffer (disruptor style) *)
(* used for multicast delivery.                                            *)
(*                                                                         *)
(* Producers claim strictly increasing sequence numbers from a shared      *)
(* counter. Each sequence maps to slot (seq % BufferSize). The producer    *)
(* writes the slot in two phases, so a torn intermediate state is visible  *)
(* in the model, and then publishes it through a per-slot availability     *)
(* marker.                                                                 *)
(*                                                                         *)
(* Every consumer reads every published sequence in order and without      *)
(* gaps. A producer may only claim sequence s if                           *)
(*     s < MinReadCursor + BufferSize,                                     *)
(* which means it never overtakes the slowest consumer by more than one    *)
(* lap of the ring.                                                        *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Producers,      \* set of producer ids
    Consumers,      \* set of consumer ids
    BufferSize,     \* number of slots in the ring
    MaxPublished    \* bound on the number of sequences, for finite checking

ASSUME /\ Producers # {}
       /\ Consumers # {}
       /\ BufferSize \in Nat \ {0}
       /\ MaxPublished \in Nat

NoSeq  == -1        \* "no sequence" marker
Torn   == -2        \* marker for a slot whose write is in progress (torn data)
Slots  == 0 .. (BufferSize - 1)
SeqNums == 0 .. (MaxPublished - 1)

Idx(s) == s % BufferSize

VARIABLES
    claimSeq,     \* next sequence number to hand out (shared claim counter)
    prodState,    \* [Producers -> {"idle","claimed","writing","written"}]
    prodSeq,      \* [Producers -> sequence currently owned, or NoSeq]
    buffer,       \* [Slots -> data in the slot: a seq number, NoSeq, or Torn]
    avail,        \* [Slots -> highest sequence published into that slot, or NoSeq]
    consState,    \* [Consumers -> {"idle","reading"}]
    readCursor,   \* [Consumers -> next sequence the consumer will read]
    delivered,    \* [Consumers -> Seq(data)] history of values observed
    pubSet        \* ghost: set of sequences that have ever been published

vars == << claimSeq, prodState, prodSeq, buffer, avail,
           consState, readCursor, delivered, pubSet >>

-----------------------------------------------------------------------------
MinCursor ==
    CHOOSE m \in { readCursor[c] : c \in Consumers } :
        \A c \in Consumers : m <= readCursor[c]

TypeOK ==
    /\ claimSeq \in 0 .. MaxPublished
    /\ prodState \in [Producers -> {"idle", "claimed", "writing", "written"}]
    /\ prodSeq \in [Producers -> SeqNums \cup {NoSeq}]
    /\ buffer \in [Slots -> SeqNums \cup {NoSeq, Torn}]
    /\ avail \in [Slots -> SeqNums \cup {NoSeq}]
    /\ consState \in [Consumers -> {"idle", "reading"}]
    /\ readCursor \in [Consumers -> 0 .. MaxPublished]
    /\ delivered \in [Consumers -> Seq(SeqNums \cup {NoSeq, Torn})]
    /\ pubSet \subseteq SeqNums

-----------------------------------------------------------------------------
Init ==
    /\ claimSeq   = 0
    /\ prodState  = [p \in Producers |-> "idle"]
    /\ prodSeq    = [p \in Producers |-> NoSeq]
    /\ buffer     = [i \in Slots |-> NoSeq]
    /\ avail      = [i \in Slots |-> NoSeq]
    /\ consState  = [c \in Consumers |-> "idle"]
    /\ readCursor = [c \in Consumers |-> 0]
    /\ delivered  = [c \in Consumers |-> << >>]
    /\ pubSet     = {}

-----------------------------------------------------------------------------
(* Producer actions *)

\* Atomically claim the next sequence (CAS on the claim counter), gated by
\* the wrap-around check against the slowest consumer.
Claim(p) ==
    /\ prodState[p] = "idle"
    /\ claimSeq < MaxPublished
    /\ claimSeq < MinCursor + BufferSize
    /\ prodSeq'   = [prodSeq EXCEPT ![p] = claimSeq]
    /\ prodState' = [prodState EXCEPT ![p] = "claimed"]
    /\ claimSeq'  = claimSeq + 1
    /\ UNCHANGED << buffer, avail, consState, readCursor, delivered, pubSet >>

\* Start writing: the slot contents become inconsistent (torn).
BeginWrite(p) ==
    /\ prodState[p] = "claimed"
    /\ buffer'    = [buffer EXCEPT ![Idx(prodSeq[p])] = Torn]
    /\ prodState' = [prodState EXCEPT ![p] = "writing"]
    /\ UNCHANGED << claimSeq, prodSeq, avail, consState, readCursor, delivered, pubSet >>

\* Finish writing: the slot holds the full item for this sequence.
EndWrite(p) ==
    /\ prodState[p] = "writing"
    /\ buffer'    = [buffer EXCEPT ![Idx(prodSeq[p])] = prodSeq[p]]
    /\ prodState' = [prodState EXCEPT ![p] = "written"]
    /\ UNCHANGED << claimSeq, prodSeq, avail, consState, readCursor, delivered, pubSet >>

\* Publish: mark the slot available for this round/sequence.
Publish(p) ==
    /\ prodState[p] = "written"
    /\ avail'     = [avail EXCEPT ![Idx(prodSeq[p])] = prodSeq[p]]
    /\ pubSet'    = pubSet \cup {prodSeq[p]}
    /\ prodState' = [prodState EXCEPT ![p] = "idle"]
    /\ prodSeq'   = [prodSeq EXCEPT ![p] = NoSeq]
    /\ UNCHANGED << claimSeq, buffer, consState, readCursor, delivered >>

Producer(p) == Claim(p) \/ BeginWrite(p) \/ EndWrite(p) \/ Publish(p)

-----------------------------------------------------------------------------
(* Consumer actions *)

\* A consumer may begin reading its next sequence only once it is published.
BeginRead(c) ==
    /\ consState[c] = "idle"
    /\ readCursor[c] < MaxPublished
    /\ avail[Idx(readCursor[c])] = readCursor[c]
    /\ consState' = [consState EXCEPT ![c] = "reading"]
    /\ UNCHANGED << claimSeq, prodState, prodSeq, buffer, avail,
                    readCursor, delivered, pubSet >>

\* Finish reading: record the observed data and advance the cursor.
EndRead(c) ==
    /\ consState[c] = "reading"
    /\ delivered'  = [delivered EXCEPT ![c] =
                        Append(delivered[c], buffer[Idx(readCursor[c])])]
    /\ readCursor' = [readCursor EXCEPT ![c] = readCursor[c] + 1]
    /\ consState'  = [consState EXCEPT ![c] = "idle"]
    /\ UNCHANGED << claimSeq, prodState, prodSeq, buffer, avail, pubSet >>

Consumer(c) == BeginRead(c) \/ EndRead(c)

-----------------------------------------------------------------------------
\* Termination: all sequences produced and consumed; stutter to avoid deadlock.
Done ==
    /\ claimSeq = MaxPublished
    /\ \A p \in Producers : prodState[p] = "idle"
    /\ \A c \in Consumers : consState[c] = "idle" /\ readCursor[c] = MaxPublished
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Producers : Producer(p)
    \/ \E c \in Consumers : Consumer(c)
    \/ Done

Fairness ==
    /\ \A p \in Producers : WF_vars(Producer(p))
    /\ \A c \in Consumers : WF_vars(Consumer(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

ActiveProducer(p) == prodState[p] # "idle"

\* Distinct in-flight producers own distinct sequences, and so distinct slots.
UniqueClaims ==
    \A p, q \in Producers :
        (p # q /\ ActiveProducer(p) /\ ActiveProducer(q))
            => /\ prodSeq[p] # prodSeq[q]
               /\ Idx(prodSeq[p]) # Idx(prodSeq[q])

\* Every owned sequence was handed out by the claim counter.
ClaimedSeqValid ==
    \A p \in Producers :
        ActiveProducer(p) => prodSeq[p] \in 0 .. (claimSeq - 1)

\* No data race: no consumer reads a slot that a producer owns.
NoDataRace ==
    \A p \in Producers, c \in Consumers :
        (ActiveProducer(p) /\ consState[c] = "reading")
            => Idx(prodSeq[p]) # Idx(readCursor[c])

\* Producers never overtake the slowest consumer by more than one lap.
NoOvertake ==
    /\ claimSeq <= MinCursor + BufferSize
    /\ \A p \in Producers :
         ActiveProducer(p) => prodSeq[p] < MinCursor + BufferSize

\* Consumers only read sequences that are published and fully written.
ReadOnlyPublished ==
    \A c \in Consumers :
        consState[c] = "reading" =>
            /\ avail[Idx(readCursor[c])] = readCursor[c]
            /\ buffer[Idx(readCursor[c])] = readCursor[c]
            /\ readCursor[c] \in pubSet

\* Everything a consumer has passed over was published.
ConsumedWasPublished ==
    \A c \in Consumers : \A s \in 0 .. (readCursor[c] - 1) : s \in pubSet

\* Buffer integrity under wrap-around. A published slot keeps its data
\* until every consumer has read it.
BufferIntegrity ==
    \A i \in Slots :
        (avail[i] # NoSeq /\ buffer[i] # avail[i])
            => \A c \in Consumers : readCursor[c] > avail[i]

\* Publication semantics: the availability marker is consistent with indexing
\* and with the claim counter.
PublicationCorrect ==
    /\ \A i \in Slots : avail[i] # NoSeq => (Idx(avail[i]) = i /\ avail[i] < claimSeq)
    /\ \A s \in pubSet : s < claimSeq

\* Multicast delivery: each consumer has seen exactly 0,1,2,... in order,
\* with no gaps and no torn values.
InOrderNoGaps ==
    \A c \in Consumers :
        /\ Len(delivered[c]) = readCursor[c]
        /\ delivered[c] = [k \in 1 .. readCursor[c] |-> k - 1]

\* No consumer gets ahead of what has been claimed.
CursorBounded ==
    \A c \in Consumers : readCursor[c] <= claimSeq

Safety ==
    /\ TypeOK
    /\ UniqueClaims
    /\ ClaimedSeqValid
    /\ NoDataRace
    /\ NoOvertake
    /\ ReadOnlyPublished
    /\ ConsumedWasPublished
    /\ BufferIntegrity
    /\ PublicationCorrect
    /\ InOrderNoGaps
    /\ CursorBounded

\* Action properties: cursors, the claim counter and availability markers
\* are monotonic.
Monotonic ==
    [][ /\ claimSeq' >= claimSeq
        /\ \A c \in Consumers : readCursor'[c] >= readCursor[c]
        /\ \A i \in Slots : avail'[i] >= avail[i]
        /\ pubSet \subseteq pubSet' ]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Multicast delivery: every published sequence is eventually read by every consumer.
EventualDelivery ==
    \A s \in SeqNums, c \in Consumers :
        (s \in pubSet) ~> (readCursor[c] > s)

\* Progress: whatever is published, consumers eventually catch up to it.
CatchUp ==
    \A c \in Consumers, n \in 0 .. MaxPublished :
        (\A s \in 0 .. (n - 1) : s \in pubSet) ~> (readCursor[c] >= n)

\* Every sequence within the bound is eventually published.
EventualPublication ==
    \A s \in SeqNums : <>(s \in pubSet)

\* The system eventually delivers everything to everyone and stays there.
EventualCompletion ==
    <>[](\A c \in Consumers : readCursor[c] = MaxPublished)

=============================================================================