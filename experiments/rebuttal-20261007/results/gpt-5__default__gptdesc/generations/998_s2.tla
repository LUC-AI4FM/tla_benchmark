------------------------------ MODULE ResourceAllocator ------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  CLIENTS,   \* finite, nonempty set of clients
  RESOURCES, \* finite, nonempty set of resources
  SCHED      \* nonempty finite sequence over CLIENTS (the scheduling sequence)

ASSUME
  /\ CLIENTS /= {}
  /\ RESOURCES /= {}
  /\ IsFiniteSet(CLIENTS)
  /\ IsFiniteSet(RESOURCES)
  /\ SCHED \in Seq(CLIENTS)
  /\ SCHED /= << >>

VARIABLES
  req,   \* function [CLIENTS -> SUBSET RESOURCES], the currently requested set per client ({} means no outstanding request)
  hold,  \* function [CLIENTS -> SUBSET RESOURCES], the resources currently held by each client
  pc     \* position in the schedule SCHED (1..Len(SCHED))

vars == << req, hold, pc >>

Held == UNION { hold[c] : c \in CLIENTS }
Free == RESOURCES \ Held
Full(c) == hold[c] = req[c]
Allowed(c) == SCHED[pc] = c

Init ==
  /\ req  = [c \in CLIENTS |-> {}]
  /\ hold = [c \in CLIENTS |-> {}]
  /\ pc = 1

Request(c) ==
  /\ c \in CLIENTS
  /\ req[c] = {}
  /\ hold[c] = {}
  /\ \E S \in SUBSET RESOURCES:
        /\ S /= {}
        /\ req' = [req EXCEPT ![c] = S]
  /\ UNCHANGED << hold, pc >>

Allocate(c, r) ==
  /\ c \in CLIENTS
  /\ r \in RESOURCES
  /\ Allowed(c)
  /\ r \in req[c] \ hold[c]
  /\ r \notin Held
  /\ hold' = [hold EXCEPT ![c] = hold[c] \cup {r}]
  /\ UNCHANGED << req, pc >>

ReturnSome(c) ==
  /\ c \in CLIENTS
  /\ req[c] /= hold[c]          \* only allow early returns when not fully satisfied
  /\ hold[c] /= {}
  /\ \E R \in SUBSET hold[c]:
        /\ R /= {}
        /\ hold' = [hold EXCEPT ![c] = hold[c] \ R]
  /\ UNCHANGED << req, pc >>

ReturnAll(c) ==
  /\ c \in CLIENTS
  /\ req[c] = hold[c]
  /\ req[c] /= {}
  /\ hold' = [hold EXCEPT ![c] = {}]
  /\ req'  = [req  EXCEPT ![c] = {}]
  /\ UNCHANGED pc

Tick ==
  /\ pc' = IF pc < Len(SCHED) THEN pc + 1 ELSE 1
  /\ UNCHANGED << req, hold >>

Next ==
  \/ \E c \in CLIENTS: Request(c)
  \/ \E c \in CLIENTS, r \in RESOURCES: Allocate(c, r)
  \/ \E c \in CLIENTS: ReturnSome(c)
  \/ \E c \in CLIENTS: ReturnAll(c)
  \/ Tick

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in CLIENTS: WF_vars(ReturnAll(c))        \* weak fairness: once fully satisfied, client eventually returns all
  /\ \A c \in CLIENTS: \A r \in RESOURCES: WF_vars(Allocate(c, r)) \* weak fairness: enabled allocations eventually occur
  /\ WF_vars(Tick)                                   \* weak fairness: scheduling ticks eventually occur

(************************************************************************)
(* Safety invariants                                                    *)
(************************************************************************)

TypeOK ==
  /\ req \in [CLIENTS -> SUBSET RESOURCES]
  /\ hold \in [CLIENTS -> SUBSET RESOURCES]
  /\ pc \in 1..Len(SCHED)

Mutex ==
  \A c, d \in CLIENTS: c /= d => hold[c] \cap hold[d] = {}

AllocInv ==
  /\ \A c \in CLIENTS: hold[c] \subseteq req[c]
  /\ Held \subseteq RESOURCES

SafetyInv == TypeOK /\ Mutex /\ AllocInv

(************************************************************************)
(* Liveness properties to be checked                                    *)
(************************************************************************)

EventuallyReturn ==
  \A c \in CLIENTS:
    []( (Full(c) /\ req[c] /= {}) => <> (req[c] = {} /\ hold[c] = {}) )

EventuallyObtain ==
  \A c \in CLIENTS:
    []( req[c] /= {} => <> Full(c) )

InfOftenSatisfied ==
  \A c \in CLIENTS:
    []<> Full(c)

=============================================================================