------------------------------ MODULE Bakery ------------------------------
EXTENDS Naturals

CONSTANT NumProcs, MaxNum

(* ------------------------------------------------------------------ *)
(* Types and constants *)

ProcessId == 1 .. NumProcs
PhaseVal   == {"idle", "choosing", "waiting", "critical", "releasing"}

(* ------------------------------------------------------------------ *)
(* Variables *)

VARIABLES Phase, Ticket, Choosing

(* ------------------------------------------------------------------ *)
(* Initial state *)

Init ==
    /\ Phase   = [i \in ProcessId |-> "idle"]
    /\ Ticket  = [i \in ProcessId |-> 0]
    /\ Choosing = [i \in ProcessId |-> FALSE]

(* ------------------------------------------------------------------ *)
(* Helper functions *)

MaxTicket == Max({Ticket[j] : j \in ProcessId})

(* ------------------------------------------------------------------ *)
(* Actions *)

StartEnter(i) ==
    /\ i \in ProcessId
    /\ Phase[i] = "idle"
    /\ Phase'   = [Phase EXCEPT ![i] = "choosing"]
    /\ Choosing'= [Choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED Ticket

ComputeTicket(i) ==
    /\ i \in ProcessId
    /\ Phase[i] = "choosing"
    /\ Choosing[i] = TRUE
    /\ Ticket'   = [Ticket EXCEPT ![i] = Max({Ticket[j] : j \in ProcessId}) + 1]
    /\ Choosing'= [Choosing EXCEPT ![i] = FALSE]
    /\ Phase'    = [Phase EXCEPT ![i] = "waiting"]

EnterCS(i) ==
    /\ i \in ProcessId
    /\ Phase[i] = "waiting"
    /\ \A j \in ProcessId : (j # i) =>
          Ticket[j] > Ticket[i] \/ (Ticket[j] = Ticket[i] /\ j > i)
    /\ Phase'   = [Phase EXCEPT ![i] = "critical"]

ExitCS(i) ==
    /\ i \in ProcessId
    /\ Phase[i] = "critical"
    /\ Phase'   = [Phase EXCEPT ![i] = "releasing"]

ReleaseTicket(i) ==
    /\ i \in ProcessId
    /\ Phase[i] = "releasing"
    /\ Ticket'  = [Ticket EXCEPT ![i] = 0]
    /\ Phase'   = [Phase EXCEPT ![i] = "idle"]

(* ------------------------------------------------------------------ *)
(* Next-state relation *)

Next ==
    ∃ i \in ProcessId :
        StartEnter(i) \/ ComputeTicket(i) \/ EnterCS(i) \/ ExitCS(i) \/ ReleaseTicket(i)

vars == <<Phase, Ticket, Choosing>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* ------------------------------------------------------------------ *)
(* Invariants *)

MutualExclusion ==
    \A i,j \in ProcessId : (i # j) => ~(Phase[i] = "critical" /\ Phase[j] = "critical")

TicketBound ==
    \A i \in ProcessId : Ticket[i] <= MaxNum

ResetTicket ==
    \A i \in ProcessId : (Phase[i] = "idle") => Ticket[i] = 0

OrderingInvariant ==
    \A i \in ProcessId :
        Phase[i] = "critical" =>
            \A j \in ProcessId : (j # i) =>
                Ticket[j] > Ticket[i] \/ (Ticket[j] = Ticket[i] /\ j > i)

ChoosingConsistency ==
    \A i \in ProcessId : Choosing[i] <=> Phase[i] = "choosing"

Invariant == MutualExclusion /\ TicketBound /\ ResetTicket /\ OrderingInvariant /\ ChoosingConsistency

(* ------------------------------------------------------------------ *)
(* Liveness property *)

Liveness ==
    ∀ i \in ProcessId :
        (Phase[i] = "waiting" \/ Phase[i] = "choosing") => <> (Phase[i] = "critical")

=============================================================================