---- MODULE BlockingQueue ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Producers, Consumers, BufCapacity

ASSUME Producers /= {}
ASSUME Consumers /= {}
ASSUME Producers \intersect Consumers = {}
ASSUME BufCapacity \in Nat /\ BufCapacity > 0

VARIABLES buffer, waitP, waitC

vars == <<buffer, waitP, waitC>>

RunningThreads == (Producers \cup Consumers) \ (waitP \cup waitC)

NotifyOther(ws) ==
    IF ws /= {}
    THEN \E x \in ws : ws' = ws \ {x}
    ELSE UNCHANGED ws

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
    /\ IF Len(buffer) > 0
       THEN /\ buffer' = Tail(buffer)
            /\ NotifyOther(waitP)
            /\ UNCHANGED waitC
       ELSE /\ waitC' = waitC \cup {t}
            /\ UNCHANGED <<buffer, waitP>>

Init ==
    /\ buffer = <<>>
    /\ waitP = {}
    /\ waitC = {}

Next ==
    \/ \E p \in Producers : Put(p, p)
    \/ \E c \in Consumers : Get(c)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ buffer \in Seq(Producers)
    /\ Len(buffer) \in 0..BufCapacity
    /\ waitP \subseteq Producers
    /\ waitC \subseteq Consumers

Inv == ~(waitP = Producers /\ waitC = Consumers)

====