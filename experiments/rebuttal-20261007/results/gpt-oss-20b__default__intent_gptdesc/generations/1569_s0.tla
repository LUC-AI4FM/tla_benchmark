------------------------------ MODULE Bakery ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, MaxTicket

VARIABLES ticket, choosing, phase

(* -- type invariant ----------------------------------------------------- *)
TypeInv == /\ ticket \in [1..N -> 0..MaxTicket]
          /\ choosing \in [1..N -> BOOLEAN]
          /\ phase   \in [1..N -> {"idle","choosing","waiting","critical"}]

(* -- initial state ------------------------------------------------------ *)
Init ==
    /\ ticket = [i \in 1..N |-> 0]
    /\ choosing = [i \in 1..N |-> FALSE]
    /\ phase   = [i \in 1..N |-> "idle"]
    /\ TypeInv

(* -- actions ------------------------------------------------------------ *)

StartChoosing(i) ==
    /\ i \in 1..N
    /\ phase[i] = "idle"
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ phase'   = [phase EXCEPT ![i] = "choosing"]
    /\ ticket'  = ticket

SetTicket(i) ==
    /\ i \in 1..N
    /\ phase[i] = "choosing"
    /\ choosing[i] = TRUE
    LET others == {j \in 1..N : j # i}
        maxOther == IF others = {} THEN 0 ELSE MAX({ticket[j] : j \in others})
    IN /\ ticket'   = [ticket EXCEPT ![i] = 1 + maxOther]
       /\ choosing' = [choosing EXCEPT ![i] = FALSE]
       /\ phase'    = [phase EXCEPT ![i] = "waiting"]

Wait(i) ==
    /\ i \in 1..N
    /\ phase[i] = "waiting"
    /\ NOT (\E j \in 1..N : j # i /\ (choosing[j] \/ (ticket[j] /= 0 /\ (ticket[j] < ticket[i] \/ (ticket[j] = ticket[i] /\ j < i)))))
    /\ phase'   = [phase EXCEPT ![i] = "critical"]
    /\ choosing'= choosing
    /\ ticket'  = ticket

Release(i) ==
    /\ i \in 1..N
    /\ phase[i] = "critical"
    /\ ticket'  = [ticket EXCEPT ![i] = 0]
    /\ phase'   = [phase EXCEPT ![i] = "idle"]
    /\ choosing'= choosing

Next == ∃ i \in 1..N : StartChoosing(i) \/ SetTicket(i) \/ Wait(i) \/ Release(i)

Spec == Init /\ [][Next]_<<ticket, choosing, phase>> /\ TypeInv

(* -- invariants -------------------------------------------------------- *)

MutualExcl ==
    \A i,j \in 1..N :
        (phase[i] = "critical" /\ phase[j] = "critical") => i = j

TicketBound ==
    \A i \in 1..N : ticket[i] <= MaxTicket

ResetAfterLeave ==
    \A i \in 1..N : (phase[i] = "idle") => ticket[i] = 0

ChoosingInvariant ==
    \A i \in 1..N : choosing[i] => phase[i] = "choosing"

WaitConditionInvariant ==
    \A i \in 1..N :
        (phase[i] = "waiting") =>
            NOT (\E j \in 1..N : j # i /\ (choosing[j] \/ (ticket[j] /= 0 /\ (ticket[j] < ticket[i] \/ (ticket[j] = ticket[i] /\ j < i)))))

(* -- liveness ---------------------------------------------------------- *)

Liveness ==
    WF_∃i (Wait(i))

SpecWithFairness == Spec /\ Liveness

=============================================================================