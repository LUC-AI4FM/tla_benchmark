---------------------------- MODULE BlockingQueue ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Producers,   \* set of producer process identifiers
          Consumers,   \* set of consumer process identifiers
          BufCapacity  \* maximum number of items in the buffer

ASSUME /\ Producers # {}
       /\ Consumers # {}
       /\ Producers \intersect Consumers = {}
       /\ BufCapacity \in Nat
       /\ BufCapacity > 0

VARIABLES buffer, \* sequence of items currently in the buffer
          waitP,  \* set of producers currently blocked
          waitC   \* set of consumers currently blocked

vars == <<buffer, waitP, waitC>>

-----------------------------------------------------------------------------

TypeOK ==
    /\ buffer \in Seq(Producers)
    /\ Len(buffer) \in 0..BufCapacity
    /\ waitP \subseteq Producers
    /\ waitC \subseteq Consumers

Init ==
    /\ buffer = <<>>
    /\ waitP = {}
    /\ waitC = {}

-----------------------------------------------------------------------------

(* Wake (at most) one waiting consumer, if any is waiting. *)
WakeConsumer ==
    IF waitC # {}
    THEN \E x \in waitC : waitC' = waitC \ {x}
    ELSE UNCHANGED waitC

(* Wake (at most) one waiting producer, if any is waiting. *)
WakeProducer ==
    IF waitP # {}
    THEN \E x \in waitP : waitP' = waitP \ {x}
    ELSE UNCHANGED waitP

(* Producer step *)
p(self) ==
    /\ self \notin waitP
    /\ IF Len(buffer) = BufCapacity
       THEN /\ waitP' = waitP \cup {self}
            /\ UNCHANGED <<buffer, waitC>>
       ELSE /\ buffer' = Append(buffer, self)
            /\ WakeConsumer
            /\ UNCHANGED waitP

(* Consumer step *)
c(self) ==
    /\ self \notin waitC
    /\ IF buffer = <<>>
       THEN /\ waitC' = waitC \cup {self}
            /\ UNCHANGED <<buffer, waitP>>
       ELSE /\ buffer' = Tail(buffer)
            /\ WakeProducer
            /\ UNCHANGED waitC

Next ==
    \/ \E self \in Producers : p(self)
    \/ \E self \in Consumers : c(self)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

(* Deadlock freedom: never are all producers and all consumers blocked. *)
Inv == ~(waitP = Producers /\ waitC = Consumers)

=============================================================================