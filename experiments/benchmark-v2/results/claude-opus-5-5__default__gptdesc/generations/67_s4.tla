--------------------------- MODULE BlockingQueueSplit ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Producers,   \* a nonempty set of producers
          Consumers,   \* a nonempty set of consumers
          BufCapacity  \* the maximum number of messages in the bounded buffer

ASSUME Assumption ==
    /\ Producers # {}
    /\ Consumers # {}
    /\ Producers \intersect Consumers = {}
    /\ BufCapacity \in (Nat \ {0})

-----------------------------------------------------------------------------

VARIABLES buffer, waitP, waitC

vars == <<buffer, waitP, waitC>>

TypeOK ==
    /\ buffer \in Seq(Producers)
    /\ Len(buffer) \in 0..BufCapacity
    /\ waitP \subseteq Producers
    /\ waitC \subseteq Consumers

\* Wake up one arbitrary waiting process from ws, if there is one.
NotifyOther(ws) ==
    IF ws # {}
    THEN \E x \in ws : ws' = ws \ {x}
    ELSE UNCHANGED ws

-----------------------------------------------------------------------------

Put(t, d) ==
    /\ t \notin waitP
    /\ IF Len(buffer) < BufCapacity
       THEN /\ buffer' = Append(buffer, d)
            /\ NotifyOther(waitC)
            /\ UNCHANGED waitP
       ELSE /\ waitP' = waitP \cup {t}
            /\ UNCHANGED <<buffer, waitC>>

Get(t) ==
    /\ t \notin waitC
    /\ IF buffer # <<>>
       THEN /\ buffer' = Tail(buffer)
            /\ NotifyOther(waitP)
            /\ UNCHANGED waitC
       ELSE /\ waitC' = waitC \cup {t}
            /\ UNCHANGED <<buffer, waitP>>

-----------------------------------------------------------------------------

Init ==
    /\ buffer = <<>>
    /\ waitP = {}
    /\ waitC = {}

Next ==
    \/ \E p \in Producers : Put(p, p)
    \/ \E c \in Consumers : Get(c)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* Not all producers and all consumers are waiting at the same time.
Invariant == ~ (waitP = Producers /\ waitC = Consumers)

=============================================================================