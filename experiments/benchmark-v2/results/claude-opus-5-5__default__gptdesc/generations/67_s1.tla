--------------------------- MODULE BlockingQueue ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Producers,   (* the (nonempty) set of producers                *)
          Consumers,   (* the (nonempty) set of consumers                *)
          BufCapacity  (* the maximum number of messages in the buffer   *)

ASSUME Assumption ==
       /\ Producers # {}
       /\ Consumers # {}
       /\ Producers \intersect Consumers = {}
       /\ BufCapacity \in (Nat \ {0})

-----------------------------------------------------------------------------

VARIABLES buffer, waitC, waitP

vars == <<buffer, waitC, waitP>>

-----------------------------------------------------------------------------

(* Wake up some waiting process from ws, if there is one. *)
NotifyOther(ws) ==
    \/ /\ ws = {}
       /\ UNCHANGED ws
    \/ /\ ws # {}
       /\ \E x \in ws : ws' = ws \ {x}

(* Process t suspends itself by joining the wait set ws. *)
Wait(ws, t) ==
    /\ ws' = ws \cup {t}
    /\ UNCHANGED <<buffer>>

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
    /\ waitC = {}
    /\ waitP = {}

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

(* Not all producers and consumers are waiting simultaneously. *)
NoDeadlock ==
    (waitC \cup waitP) # (Producers \cup Consumers)

THEOREM Spec => [](TypeInv /\ NoDeadlock)

=============================================================================