---------------------------- MODULE AsyncInterface ----------------------------
(***************************************************************************)
(* An asynchronous single-writer / single-reader interface.                *)
(*                                                                         *)
(* A single data slot `val` carries values from a producer to a consumer.  *)
(* Two unbounded nonnegative counters coordinate them:                     *)
(*   rdy : advanced only by the producer each time it publishes a datum.   *)
(*   ack : advanced only by the consumer each time it consumes a datum.    *)
(* No synchronous handshake is assumed. The producer may write at any time *)
(* and may override a value that has not been read yet. The consumer reads *)
(* whenever rdy > ack, which means some published write is still pending.  *)
(* Steps interleave arbitrarily, and either agent may be delayed for any   *)
(* finite time.                                                            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Data              \* finite set of possible data values

ASSUME DataNonEmpty == Data # {}

NoVal == CHOOSE v : v \notin Data   \* the consumer has observed nothing yet

VARIABLES
    val,      \* the shared data slot
    rdy,      \* producer's ready counter
    ack,      \* consumer's acknowledgement counter
    out,      \* last datum observed by the consumer
    written   \* history: set of every datum the producer has written

vars == <<val, rdy, ack, out, written>>

TypeOK ==
    /\ val \in Data
    /\ rdy \in Nat
    /\ ack \in Nat
    /\ out \in Data \cup {NoVal}
    /\ written \subseteq Data

-----------------------------------------------------------------------------
Init ==
    /\ val \in Data          \* arbitrary initial contents; not yet published
    /\ rdy = 0
    /\ ack = 0
    /\ out = NoVal
    /\ written = {}

(* The producer writes datum d and advances its ready counter. It never  *)
(* waits for the consumer, so the interface never blocks the producer.   *)
SendVal(d) ==
    /\ val' = d
    /\ rdy' = rdy + 1
    /\ written' = written \cup {d}
    /\ UNCHANGED <<ack, out>>

Send == \E d \in Data : SendVal(d)

(* The consumer reads the currently published datum and acknowledges     *)
(* every write it has seen. A newer value overrides any older writes the *)
(* consumer did not read.                                                *)
Rcv ==
    /\ rdy > ack
    /\ out' = val
    /\ ack' = rdy
    /\ UNCHANGED <<val, rdy, written>>

Next == Send \/ Rcv

Spec == Init /\ [][Next]_vars /\ WF_vars(Send) /\ WF_vars(Rcv)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* The consumer never observes a datum that was never written.
NoPhantomRead == out # NoVal => out \in written

\* Whenever a write is pending, the slot holds a value that was written.
PendingValueWritten == rdy > ack => val \in written

\* Both counters remain nonnegative integers.
CountersNonNeg == rdy \in Nat /\ ack \in Nat /\ rdy >= 0 /\ ack >= 0

\* The consumer never acknowledges more writes than were published.
AckBounded == ack <= rdy

SafetyInv ==
    /\ TypeOK
    /\ NoPhantomRead
    /\ PendingValueWritten
    /\ CountersNonNeg
    /\ AckBounded

\* Only the producer changes rdy, and only the consumer changes ack.
\* Neither counter ever decreases.
CounterOwnership ==
    [][ /\ (rdy' # rdy => Send /\ rdy' > rdy)
        /\ (ack' # ack => Rcv  /\ ack' > ack) ]_vars

\* The written history only grows.
HistoryMonotone == [][written \subseteq written']_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

Pending(n) == ack < n /\ n <= rdy     \* write number n published but not acked

\* Eventual delivery: each published write is eventually consumed. It is
\* either read directly or overridden by a newer write that is read.
EventualDelivery == \A n \in Nat : (rdy >= n) ~> (ack >= n)

\* Every pending value is eventually observed by the consumer.
ConsumerObserves == (rdy > ack) ~> (ack = rdy \/ <<Rcv>>_vars)

\* Producer progress: the producer can always eventually publish again.
ProducerNeverBlocked == []ENABLED Send
ProducerProgress     == []<><<Send>>_vars

\* Consumer progress: once a write is pending, the consumer eventually
\* increments its ack counter.
ConsumerProgress == \A n \in Nat : (ack = n /\ rdy > n) ~> (ack > n)

\* Handshake completion: an acknowledged write is eventually, and from then
\* on permanently, no longer pending.
HandshakeCompletes == \A n \in Nat : (ack >= n) ~> [](~Pending(n))

Liveness ==
    /\ EventualDelivery
    /\ ProducerProgress
    /\ ConsumerProgress
    /\ HandshakeCompletes

-----------------------------------------------------------------------------
THEOREM Spec => []SafetyInv
THEOREM Spec => CounterOwnership /\ HistoryMonotone
THEOREM Spec => ProducerNeverBlocked
THEOREM Spec => Liveness
=============================================================================