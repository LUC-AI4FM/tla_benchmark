------------------------------- MODULE Barrier -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

VARIABLES pc, arrived

vars == <<pc, arrived>>

Procs == 1..N

States == {"working", "waiting", "crossed"}

TypeOK ==
    /\ pc \in [Procs -> States]
    /\ arrived \subseteq Procs

Init ==
    /\ pc = [p \in Procs |-> "working"]
    /\ arrived = {}

(* A process reaches the barrier and signals arrival. *)
Arrive(p) ==
    /\ pc[p] = "working"
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ arrived' = arrived \cup {p}

(* A waiting process may pass the barrier only once all N have arrived. *)
Cross(p) ==
    /\ pc[p] = "waiting"
    /\ arrived = Procs
    /\ pc' = [pc EXCEPT ![p] = "crossed"]
    /\ UNCHANGED arrived

(* All processes have crossed: system terminates (stutters). *)
Terminating ==
    /\ \A p \in Procs : pc[p] = "crossed"
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Procs : Arrive(p) \/ Cross(p)
    \/ Terminating

Fairness ==
    \A p \in Procs : WF_vars(Arrive(p)) /\ WF_vars(Cross(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety: no process crosses before all have arrived. *)
NoPrematureCrossing ==
    \A p \in Procs : pc[p] = "crossed" => \A q \in Procs : pc[q] \in {"waiting", "crossed"}

ArrivedConsistent ==
    \A p \in Procs : (p \in arrived) <=> (pc[p] # "working")

Safety == NoPrematureCrossing /\ ArrivedConsistent

(* Liveness: once all have arrived, all eventually cross. *)
AllArrived == arrived = Procs

AllCrossed == \A p \in Procs : pc[p] = "crossed"

Progress == AllArrived ~> AllCrossed

(* Fairness: no process waits forever once the barrier condition holds. *)
NoStarvation == \A p \in Procs : (pc[p] = "waiting" /\ AllArrived) ~> (pc[p] = "crossed")

EventuallyAllCross == <>AllCrossed

=============================================================================