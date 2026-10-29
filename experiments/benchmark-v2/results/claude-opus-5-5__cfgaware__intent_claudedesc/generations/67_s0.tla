---------------------------- MODULE BlockingQueue ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Producers,   \* set of producer process identifiers
          Consumers,   \* set of consumer process identifiers
          BufCapacity  \* maximum number of items in the buffer

ASSUME Assumption ==
    /\ Producers # {}
    /\ Consumers # {}
    /\ Producers \intersect Consumers = {}
    /\ BufCapacity \in (Nat \ {0})

-----------------------------------------------------------------------------

VARIABLES buffer,   \* the shared bounded buffer (a sequence)
          waitSet   \* the set of suspended (waiting) processes

vars == <<buffer, waitSet>>

RunningThreads == (Producers \cup Consumers) \ waitSet

(* Wake one waiting process of the "other" kind, if any is waiting.          *)
(* A producer wakes a waiting consumer; a consumer wakes a waiting producer. *)
NotifyOther(t) ==
    LET S == IF t \in Producers
               THEN waitSet \ Producers
               ELSE waitSet \ Consumers
    IN  IF S # {}
          THEN \E x \in S : waitSet' = waitSet \ {x}
          ELSE UNCHANGED waitSet

(* Suspend process t in the wait set. *)
Wait(t) ==
    /\ waitSet' = waitSet \cup {t}
    /\ UNCHANGED buffer

-----------------------------------------------------------------------------

Put(t, d) ==
    \/ /\ Len(buffer) < BufCapacity
       /\ buffer' = Append(buffer, d)
       /\ NotifyOther(t)
    \/ /\ Len(buffer) = BufCapacity
       /\ Wait(t)

Get(t) ==
    \/ /\ buffer # <<>>
       /\ buffer' = Tail(buffer)
       /\ NotifyOther(t)
    \/ /\ buffer = <<>>
       /\ Wait(t)

-----------------------------------------------------------------------------

TypeOK ==
    /\ buffer \in Seq(Producers)
    /\ Len(buffer) \in 0..BufCapacity
    /\ waitSet \subseteq (Producers \cup Consumers)

Init ==
    /\ buffer = <<>>
    /\ waitSet = {}

Next ==
    \/ \E p \in RunningThreads \cap Producers : Put(p, p)
    \/ \E c \in RunningThreads \cap Consumers : Get(c)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

(* Safety: never are all producers and all consumers waiting at once. *)
Inv == ~(Producers \subseteq waitSet /\ Consumers \subseteq waitSet)

=============================================================================