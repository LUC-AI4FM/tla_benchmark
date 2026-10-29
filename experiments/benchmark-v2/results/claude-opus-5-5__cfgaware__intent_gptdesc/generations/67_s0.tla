---------------------------- MODULE BoundedBuffer ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Producers, Consumers, BufCapacity

ASSUME /\ Producers # {}
       /\ Consumers # {}
       /\ Producers \cap Consumers = {}
       /\ BufCapacity \in Nat
       /\ BufCapacity > 0

VARIABLES buffer, waitP, waitC

vars == <<buffer, waitP, waitC>>

Participants == Producers \cup Consumers

TypeOK ==
    /\ buffer \in Seq(Producers)
    /\ waitP \subseteq Producers
    /\ waitC \subseteq Consumers

-----------------------------------------------------------------------------
(* Wake one waiting thread from set W, chosen nondeterministically, or     *)
(* leave W unchanged if nobody is waiting.                                  *)
WakeOne(W, W2) ==
    IF W = {} THEN W2 = W
    ELSE \E t \in W : W2 = W \ {t}

Init ==
    /\ buffer = <<>>
    /\ waitP = {}
    /\ waitC = {}

(* An active producer attempts to append an item.                          *)
Put(p) ==
    /\ p \notin waitP
    /\ IF Len(buffer) < BufCapacity
         THEN /\ buffer' = Append(buffer, p)
              /\ WakeOne(waitC, waitC')
              /\ UNCHANGED waitP
         ELSE /\ waitP' = waitP \cup {p}
              /\ UNCHANGED <<buffer, waitC>>

(* An active consumer attempts to remove an item.                          *)
Get(c) ==
    /\ c \notin waitC
    /\ IF Len(buffer) > 0
         THEN /\ buffer' = Tail(buffer)
              /\ WakeOne(waitP, waitP')
              /\ UNCHANGED waitC
         ELSE /\ waitC' = waitC \cup {c}
              /\ UNCHANGED <<buffer, waitP>>

Next ==
    \/ \E p \in Producers : Put(p)
    \/ \E c \in Consumers : Get(c)

Fairness ==
    /\ \A p \in Producers : WF_vars(Put(p))
    /\ \A c \in Consumers : WF_vars(Get(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

BufferBounds == 0 <= Len(buffer) /\ Len(buffer) <= BufCapacity

NoDoubleWaiting == \A t \in Participants : ~(t \in waitP /\ t \in waitC)

NoGlobalDeadlock == ~(waitP = Producers /\ waitC = Consumers)

Inv ==
    /\ TypeOK
    /\ BufferBounds
    /\ NoDoubleWaiting
    /\ NoGlobalDeadlock

(* Liveness-style properties *)

ResumedProducerProgress ==
    \A p \in Producers :
        (p \in waitP) ~> (p \notin waitP \/ Len(buffer) = BufCapacity)

ResumedConsumerProgress ==
    \A c \in Consumers :
        (c \in waitC) ~> (c \notin waitC \/ Len(buffer) = 0)

Progress == []<>(ENABLED Next)

=============================================================================