---------------------------- MODULE AsynchChannel ----------------------------
EXTENDS Naturals

CONSTANTS Data,      \* finite set of data values that may be sent
          DataVal    \* initial value stored in the channel (parameter)

VARIABLES val,       \* the datum currently stored in the channel
          rdy,       \* sender's ready flag (toggled to signal new data)
          ack,       \* receiver's ack flag (toggled to acknowledge receipt)
          hasRead,   \* receiver has read the current datum but not yet acked
          lastRead,  \* value most recently read by the receiver
          written,   \* history: set of values ever written by the sender
          received   \* history: set of values ever read by the receiver

vars == <<val, rdy, ack, hasRead, lastRead, written, received>>

-----------------------------------------------------------------------------
TypeInvariant ==
    /\ val \in Data \cup {DataVal}
    /\ rdy \in {0, 1}
    /\ ack \in {0, 1}
    /\ hasRead \in BOOLEAN
    /\ lastRead \in Data \cup {DataVal}
    /\ written \subseteq Data
    /\ received \subseteq Data

-----------------------------------------------------------------------------
\* The initial ready/ack state is a parameter of the model: any initial
\* combination where the channel is "empty" (rdy = ack) is allowed.
Init ==
    /\ val = DataVal
    /\ rdy \in {0, 1}
    /\ ack = rdy
    /\ hasRead = FALSE
    /\ lastRead = DataVal
    /\ written = {}
    /\ received = {}

\* Sender writes a datum: only permitted when the previous datum
\* (if any) has been acknowledged, i.e. rdy = ack.
Send(d) ==
    /\ rdy = ack
    /\ val' = d
    /\ rdy' = 1 - rdy
    /\ written' = written \cup {d}
    /\ UNCHANGED <<ack, hasRead, lastRead, received>>

\* Receiver reads the datum: only permitted when data is ready.
Read ==
    /\ rdy # ack
    /\ ~hasRead
    /\ hasRead' = TRUE
    /\ lastRead' = val
    /\ received' = received \cup {val}
    /\ UNCHANGED <<val, rdy, ack, written>>

\* Receiver acknowledges receipt of the datum it has read.
Ack ==
    /\ rdy # ack
    /\ hasRead
    /\ ack' = 1 - ack
    /\ hasRead' = FALSE
    /\ UNCHANGED <<val, rdy, lastRead, written, received>>

Next ==
    \/ \E d \in Data : Send(d)
    \/ Read
    \/ Ack

Fairness ==
    /\ WF_vars(Read)
    /\ WF_vars(Ack)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

\* No data loss / phantom data: receiver never claims a datum never written.
NoPhantomData == received \subseteq written

\* No corruption: while data is pending and read, the value read equals
\* the value currently written in the channel.
NoCorruption == hasRead => (lastRead = val /\ lastRead \in written)

\* No race: the sender never overwrites unacknowledged data.
NoOverwrite ==
    [][ (val' # val \/ rdy' # rdy) => (rdy = ack) ]_vars

\* Read and ack only happen when data is ready.
ReadOnlyWhenReady == hasRead => rdy # ack

Safety ==
    /\ TypeInvariant
    /\ NoPhantomData
    /\ NoCorruption
    /\ ReadOnlyWhenReady

-----------------------------------------------------------------------------
\* Liveness properties

\* Every write is eventually read and acknowledged.
EventuallyAcked == (rdy # ack) ~> (rdy = ack)

\* Every written datum is eventually read.
EventuallyRead == \A d \in Data : (rdy # ack /\ val = d) ~> (lastRead = d /\ hasRead)

\* The channel never remains stuck in an intermediate state.
NoPermanentStall == []<>(rdy = ack)

THEOREM Spec => []Safety /\ NoOverwrite
THEOREM Spec => EventuallyAcked /\ NoPermanentStall
=============================================================================