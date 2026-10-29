---------------------------- MODULE BlockingQueue ----------------------------
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

-----------------------------------------------------------------------------

\* Wake up some arbitrary waiting thread from the given wait set, if any.
NotifyOther(ws) ==
    IF ws # {}
    THEN \E x \in ws : ws' = ws \ {x}
    ELSE UNCHANGED ws

\* Put thread t into the given wait set.
Wait(ws, t) ==
    /\ ws' = ws \cup {t}
    /\ UNCHANGED buffer

-----------------------------------------------------------------------------

Put(t, d) ==
    /\ t \notin waitP
    /\ \/ /\ Len(buffer) < BufCapacity
          /\ buffer' = Append(buffer, d)
          /\ NotifyOther(waitC)
          /\ UNCHANGED waitP
       \/ /\ Len(buffer) = BufCapacity
          /\ Wait(waitP, t)
          /\ UNCHANGED waitC

Get(t) ==
    /\ t \notin waitC
    /\ \/ /\ buffer # <<>>
          /\ buffer' = Tail(buffer)
          /\ NotifyOther(waitP)
          /\ UNCHANGED waitC
       \/ /\ buffer = <<>>
          /\ Wait(waitC, t)
          /\ UNCHANGED waitP

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

TypeInv ==
    /\ buffer \in Seq(Producers)
    /\ Len(buffer) \in 0..BufCapacity
    /\ waitP \subseteq Producers
    /\ waitC \subseteq Consumers

\* Not all producers and all consumers are waiting at the same time.
NoDeadlock == ~(waitP = Producers /\ waitC = Consumers)

THEOREM Spec => [](TypeInv /\ NoDeadlock)

=============================================================================