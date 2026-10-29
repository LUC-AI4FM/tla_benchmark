---------------------------- MODULE TicketMutex ----------------------------
(***************************************************************************)
(* A ticket-lock mutual exclusion protocol for N concurrent processes.     *)
(*                                                                         *)
(* A process that wants the critical section atomically takes the next     *)
(* ticket (fetch-and-increment on nextTicket). It then waits until         *)
(* nowServing equals its ticket, enters the critical section, and on exit  *)
(* advances nowServing.                                                    *)
(*                                                                         *)
(* At most N tickets are outstanding at any time, because each process     *)
(* holds at most one. So the counters can be kept modulo N, which keeps    *)
(* the state space finite for model checking.                              *)
(*                                                                         *)
(* The protocol serves processes in FIFO order. This guarantees            *)
(* starvation freedom under weak fairness of the protocol steps.           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N            \* number of processes (e.g. 3 for model checking)

ASSUME NAssump == N \in Nat \ {0}

Procs == 1..N

VARIABLES
    pc,          \* pc[p] \in {"ncs", "wait", "cs"}
    ticket,      \* ticket[p] : ticket held by process p
    nextTicket,  \* next ticket number to be handed out (mod N)
    nowServing   \* ticket number currently allowed into the CS (mod N)

vars == << pc, ticket, nextTicket, nowServing >>

Tickets == 0..(N-1)

TypeOK ==
    /\ pc \in [Procs -> {"ncs", "wait", "cs"}]
    /\ ticket \in [Procs -> Tickets]
    /\ nextTicket \in Tickets
    /\ nowServing \in Tickets

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ ticket = [p \in Procs |-> 0]
    /\ nextTicket = 0
    /\ nowServing = 0

(* Process p leaves its noncritical section and draws a ticket.            *)
Request(p) ==
    /\ pc[p] = "ncs"
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
    /\ nextTicket' = (nextTicket + 1) % N
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED nowServing

(* Process p enters the critical section when its ticket is being served.  *)
Enter(p) ==
    /\ pc[p] = "wait"
    /\ ticket[p] = nowServing
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED << ticket, nextTicket, nowServing >>

(* Process p leaves the critical section and passes the lock on.           *)
Exit(p) ==
    /\ pc[p] = "cs"
    /\ nowServing' = (nowServing + 1) % N
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED << ticket, nextTicket >>

Next == \E p \in Procs : Request(p) \/ Enter(p) \/ Exit(p)

(***************************************************************************)
(* Fairness: a process may stay in its noncritical section forever, so     *)
(* Request has no fairness. Once a process is engaged in the protocol,     *)
(* its Enter and Exit steps are weakly fair. Exit being fair means no      *)
(* process stays in the critical section forever.                          *)
(***************************************************************************)
Fairness == \A p \in Procs : WF_vars(Enter(p)) /\ WF_vars(Exit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* Auxiliary invariant: active processes hold distinct tickets. *)
DistinctTickets ==
    \A p, q \in Procs :
        (p # q /\ pc[p] \in {"wait", "cs"} /\ pc[q] \in {"wait", "cs"})
            => ticket[p] # ticket[q]

(* Auxiliary invariant: a process in the CS holds the served ticket. *)
CSHoldsServing ==
    \A p \in Procs : pc[p] = "cs" => ticket[p] = nowServing

(* Auxiliary invariant: the number of active processes equals the number  *)
(* of tickets handed out but not yet retired, modulo N.                   *)
ActiveCount ==
    Cardinality({p \in Procs : pc[p] \in {"wait", "cs"}}) % N
        = (nextTicket - nowServing + N) % N

-----------------------------------------------------------------------------
(* Liveness *)

StarvationFreedom ==
    \A p \in Procs : (pc[p] = "wait") ~> (pc[p] = "cs")

(* Every process in the critical section eventually leaves it. *)
EventualExit ==
    \A p \in Procs : (pc[p] = "cs") ~> (pc[p] = "ncs")

DeadlockFreedom ==
    (\E p \in Procs : pc[p] = "wait") ~> (\E p \in Procs : pc[p] = "cs")

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ MutualExclusion /\ DistinctTickets /\ CSHoldsServing)
THEOREM Spec => StarvationFreedom /\ EventualExit /\ DeadlockFreedom
=============================================================================