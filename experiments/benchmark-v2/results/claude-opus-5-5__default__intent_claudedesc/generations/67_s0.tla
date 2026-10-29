---------------------------- MODULE BlockingQueue ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Producers,   \* set of producer process identifiers
          Consumers,   \* set of consumer process identifiers
          BufCapacity  \* maximum number of items in the shared buffer

ASSUME Assumption ==
    /\ Producers # {}
    /\ Consumers # {}
    /\ Producers \cap Consumers = {}
    /\ BufCapacity \in Nat
    /\ BufCapacity >= 1

VARIABLES buffer,   \* the shared bounded buffer
          waitSet   \* the set of suspended (waiting) processes

vars == <<buffer, waitSet>>

RunningThreads == (Producers \cup Consumers) \ waitSet

-----------------------------------------------------------------------------

(* Wake up one arbitrary waiting process of the opposite kind, if any. *)
NotifyOther(t) ==
    LET S == IF t \in Producers
             THEN waitSet \ Producers
             ELSE waitSet \ Consumers
    IN  IF S # {}
        THEN \E x \in S : waitSet' = waitSet \ {x}
        ELSE UNCHANGED waitSet

(* Suspend process t. *)
Wait(t) ==
    /\ waitSet' = waitSet \cup {t}
    /\ UNCHANGED buffer

-----------------------------------------------------------------------------

Put(t, d) ==
    /\ t \notin waitSet
    /\ \/ /\ Len(buffer) < BufCapacity
          /\ buffer' = Append(buffer, d)
          /\ NotifyOther(t)
       \/ /\ Len(buffer) = BufCapacity
          /\ Wait(t)

Get(t) ==
    /\ t \notin waitSet
    /\ \/ /\ buffer # <<>>
          /\ buffer' = Tail(buffer)
          /\ NotifyOther(t)
       \/ /\ buffer = <<>>
          /\ Wait(t)

-----------------------------------------------------------------------------

Init ==
    /\ buffer = <<>>
    /\ waitSet = {}

Next ==
    \/ \E p \in Producers : Put(p, p)
    \/ \E c \in Consumers : Get(c)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------

TypeOK ==
    /\ buffer \in Seq(Producers)
    /\ Len(buffer) \in 0..BufCapacity
    /\ waitSet \subseteq (Producers \cup Consumers)

BoundedBuffer == Len(buffer) <= BufCapacity

(* Key safety property: never are all producers and all consumers waiting. *)
NoDeadlock == waitSet # (Producers \cup Consumers)

THEOREM Spec => [](TypeOK /\ BoundedBuffer /\ NoDeadlock)

=============================================================================