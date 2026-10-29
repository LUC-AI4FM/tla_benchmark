---------------------------- MODULE BlockingQueuePC ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Producers,   \* set of producer process identifiers
          Consumers,   \* set of consumer process identifiers
          BufCapacity  \* maximum number of items in the buffer

ASSUME /\ Producers # {}
       /\ Consumers # {}
       /\ Producers \intersect Consumers = {}
       /\ BufCapacity \in Nat
       /\ BufCapacity > 0

VARIABLES buffer,  \* sequence of items currently in the buffer
          waitP,   \* set of blocked producers
          waitC    \* set of blocked consumers

vars == <<buffer, waitP, waitC>>

TypeOK ==
    /\ buffer \in Seq(Producers)
    /\ Len(buffer) \in 0..BufCapacity
    /\ waitP \subseteq Producers
    /\ waitC \subseteq Consumers

-----------------------------------------------------------------------------

\* Wake up one waiting process from the given wait set, if any.
NotifyC ==
    IF waitC # {}
    THEN \E x \in waitC : waitC' = waitC \ {x}
    ELSE UNCHANGED waitC

NotifyP ==
    IF waitP # {}
    THEN \E x \in waitP : waitP' = waitP \ {x}
    ELSE UNCHANGED waitP

Init ==
    /\ buffer = <<>>
    /\ waitP = {}
    /\ waitC = {}

\* Producer step
p(self) ==
    /\ self \notin waitP
    /\ IF Len(buffer) = BufCapacity
       THEN /\ waitP' = waitP \cup {self}
            /\ UNCHANGED <<buffer, waitC>>
       ELSE /\ buffer' = Append(buffer, self)
            /\ NotifyC
            /\ UNCHANGED waitP

\* Consumer step
c(self) ==
    /\ self \notin waitC
    /\ IF buffer = <<>>
       THEN /\ waitC' = waitC \cup {self}
            /\ UNCHANGED <<buffer, waitP>>
       ELSE /\ buffer' = Tail(buffer)
            /\ NotifyP
            /\ UNCHANGED waitC

Next ==
    \/ \E self \in Producers : p(self)
    \/ \E self \in Consumers : c(self)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* Deadlock freedom: never are all producers and all consumers blocked at once.
Inv == ~(waitP = Producers /\ waitC = Consumers)

=============================================================================