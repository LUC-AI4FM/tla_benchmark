---------------------------- MODULE BlockingQueueSplit ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Producers,   (* the (nonempty) set of producers                       *)
          Consumers,   (* the (nonempty) set of consumers                       *)
          BufCapacity  (* the maximum number of messages in the bounded buffer  *)

ASSUME Assumption ==
       /\ Producers # {}
       /\ Consumers # {}
       /\ Producers \intersect Consumers = {}
       /\ BufCapacity \in (Nat \ {0})

-----------------------------------------------------------------------------

VARIABLES buffer,    (* the bounded buffer, a sequence of messages *)
          waitSetC,  (* the set of currently waiting consumers     *)
          waitSetP   (* the set of currently waiting producers     *)

vars == <<buffer, waitSetC, waitSetP>>

-----------------------------------------------------------------------------

(* Wake up one (arbitrary) waiting thread in ws, if any. *)
NotifyOther(ws) ==
    IF ws # {}
    THEN \E x \in ws : ws' = ws \ {x}
    ELSE UNCHANGED ws

(* Thread t joins the wait set ws; the buffer is not modified. *)
Wait(ws, t) ==
    /\ ws' = ws \cup {t}
    /\ UNCHANGED buffer

-----------------------------------------------------------------------------

(* A producer t either waits (buffer full) or appends d and notifies a consumer. *)
Put(t, d) ==
    /\ t \notin waitSetP
    /\ \/ /\ Len(buffer) < BufCapacity
          /\ buffer' = Append(buffer, d)
          /\ NotifyOther(waitSetC)
          /\ UNCHANGED waitSetP
       \/ /\ Len(buffer) = BufCapacity
          /\ Wait(waitSetP, t)
          /\ UNCHANGED waitSetC

(* A consumer t either waits (buffer empty) or removes the head and notifies a producer. *)
Get(t) ==
    /\ t \notin waitSetC
    /\ \/ /\ buffer # <<>>
          /\ buffer' = Tail(buffer)
          /\ NotifyOther(waitSetP)
          /\ UNCHANGED waitSetC
       \/ /\ buffer = <<>>
          /\ Wait(waitSetC, t)
          /\ UNCHANGED waitSetP

-----------------------------------------------------------------------------

Init ==
    /\ buffer = <<>>
    /\ waitSetC = {}
    /\ waitSetP = {}

Next ==
    \/ \E p \in Producers : Put(p, p)
    \/ \E c \in Consumers : Get(c)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeInv ==
    /\ buffer \in Seq(Producers)
    /\ Len(buffer) \in 0..BufCapacity
    /\ waitSetP \subseteq Producers
    /\ waitSetC \subseteq Consumers

(* Not all producers and all consumers are waiting at the same time. *)
NoDeadlock ==
    ~(waitSetP = Producers /\ waitSetC = Consumers)

THEOREM Spec => [](TypeInv /\ NoDeadlock)

=============================================================================