---------------------------- MODULE BoundedBuffer ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Producers,    \* nonempty set of producer threads
          Consumers,    \* nonempty set of consumer threads
          BufCapacity,  \* fixed positive buffer capacity
          Data          \* nonempty set of items that may be produced

ASSUME /\ Producers # {}
       /\ Consumers # {}
       /\ Producers \cap Consumers = {}
       /\ BufCapacity \in Nat
       /\ BufCapacity > 0
       /\ Data # {}

VARIABLES buffer,   \* contents of the bounded buffer
          waitP,    \* producers currently blocked (buffer was full)
          waitC     \* consumers currently blocked (buffer was empty)

vars == << buffer, waitP, waitC >>

Threads == Producers \cup Consumers

-----------------------------------------------------------------------------
(* Nondeterministically resume one waiting thread from set S, if any *)
NotifyOne(S) ==
    IF S # {}
    THEN \E t \in S : S' = S \ {t}
    ELSE UNCHANGED S

(* Producer p, not currently blocked, tries to append an item *)
Put(p) ==
    /\ p \notin waitP
    /\ IF Len(buffer) < BufCapacity
       THEN /\ \E d \in Data : buffer' = Append(buffer, d)
            /\ NotifyOne(waitC)          \* an item is now available
            /\ UNCHANGED waitP
       ELSE /\ waitP' = waitP \cup {p}   \* buffer full: block
            /\ UNCHANGED << buffer, waitC >>

(* Consumer c, not currently blocked, tries to remove an item *)
Get(c) ==
    /\ c \notin waitC
    /\ IF Len(buffer) > 0
       THEN /\ buffer' = Tail(buffer)
            /\ NotifyOne(waitP)          \* space is now available
            /\ UNCHANGED waitC
       ELSE /\ waitC' = waitC \cup {c}   \* buffer empty: block
            /\ UNCHANGED << buffer, waitP >>

-----------------------------------------------------------------------------
Init ==
    /\ buffer = << >>
    /\ waitP = {}
    /\ waitC = {}

Next ==
    \/ \E p \in Producers : Put(p)
    \/ \E c \in Consumers : Get(c)

Fairness ==
    /\ \A p \in Producers : WF_vars(Put(p))
    /\ \A c \in Consumers : WF_vars(Get(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ buffer \in Seq(Data)
    /\ waitP \subseteq Producers
    /\ waitC \subseteq Consumers

BufferBounds ==
    /\ Len(buffer) >= 0
    /\ Len(buffer) <= BufCapacity

\* No thread is marked waiting in both roles
NoDoubleWaiting == waitP \cap waitC = {}

\* No global deadlock: not all producers blocked while all consumers blocked
NoDeadlock == ~(waitP = Producers /\ waitC = Consumers)

\* A blocked producer implies the buffer is (or was) full; a blocked consumer
\* implies items are absent when it blocked; never both full and empty.
NotFullAndEmpty == ~(Len(buffer) = BufCapacity /\ Len(buffer) = 0)

Safety ==
    /\ TypeOK
    /\ BufferBounds
    /\ NoDoubleWaiting
    /\ NoDeadlock
    /\ NotFullAndEmpty

-----------------------------------------------------------------------------
(* Liveness properties *)

\* A resumed (non-waiting) producer eventually performs its operation:
\* either it appends an item or finds the buffer full; in both cases the
\* buffer is eventually nonempty.
ProducerProgress ==
    \A p \in Producers : (p \notin waitP) ~> (Len(buffer) > 0)

\* A resumed (non-waiting) consumer eventually performs its operation:
\* either it removes an item or finds the buffer empty; in both cases the
\* buffer eventually has free space.
ConsumerProgress ==
    \A c \in Consumers : (c \notin waitC) ~> (Len(buffer) < BufCapacity)

\* The system as a whole always continues to make steps (no global deadlock)
GlobalProgress ==
    []<>(ENABLED (\E p \in Producers : Put(p)) \/
         ENABLED (\E c \in Consumers : Get(c)))

Liveness == ProducerProgress /\ ConsumerProgress /\ GlobalProgress

-----------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => Liveness
=============================================================================