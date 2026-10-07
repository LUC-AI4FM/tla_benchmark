------------------------------ MODULE ResourceAllocator ------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  CLIENTS,        \* finite, nonempty set of clients
  RESOURCES,      \* finite, nonempty set of resources
  Round           \* nonempty sequence of distinct clients from CLIENTS (service order)

(*
  Assumptions on constants
*)
ASSUME
  /\ IsFiniteSet(CLIENTS) /\ CLIENTS # {}
  /\ IsFiniteSet(RESOURCES) /\ RESOURCES # {}
  /\ Round \in Seq(CLIENTS)
  /\ Len(Round) >= 1
  /\ \A i, j \in 1..Len(Round) : i # j => Round[i] # Round[j]

VARIABLES
  req,        \* [CLIENTS -> SUBSET RESOURCES] current requested set of each client
  alloc,      \* [CLIENTS -> SUBSET RESOURCES] resources currently held by each client
  turn        \* current index into Round (1..Len(Round))

vars == << req, alloc, turn >>

HeadClient == Round[turn]

AllAllocated == UNION { alloc[c] : c \in CLIENTS }

Available == RESOURCES \ AllAllocated

Outstanding(c) == req[c] \ alloc[c]
Unsatisfied(c) == Outstanding(c) # {}

(*
  Initialization: no requests, no allocations, start at turn = 1
*)
Init ==
  /\ req   = [ c \in CLIENTS |-> {} ]
  /\ alloc = [ c \in CLIENTS |-> {} ]
  /\ turn  = 1

(*
  Clients issue a (possibly nonempty) request only when they hold no resources
  and have no outstanding unsatisfied request (i.e., req = alloc = {}).
*)
IssueReq(c) ==
  /\ c \in CLIENTS
  /\ req[c] = {} /\ alloc[c] = {}
  /\ \E rr \in SUBSET RESOURCES :
        /\ rr # {}                         \* make the step effective
        /\ req'   = [req EXCEPT ![c] = rr]
        /\ UNCHANGED << alloc, turn >>

(*
  The allocator may allocate a nonempty subset of currently available
  and still-outstanding resources to the head-of-line client only.
*)
Allocate(c) ==
  /\ c \in CLIENTS
  /\ c = HeadClient
  /\ \E S \in SUBSET (Outstanding(c) \cap Available) :
        /\ S # {}
        /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
        /\ UNCHANGED << req, turn >>

(*
  Clients may return any nonempty subset of held resources early at any time.
*)
ReturnSome(c) ==
  /\ c \in CLIENTS
  /\ \E S \in SUBSET alloc[c] :
        /\ S # {}
        /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
        /\ UNCHANGED << req, turn >>

(*
  Once fully satisfied (alloc = req) and holding resources, a client
  can (and under WF will) return all resources and clear the request.
*)
ReturnWhenSatisfied(c) ==
  /\ c \in CLIENTS
  /\ alloc[c] # {}
  /\ alloc[c] = req[c]
  /\ alloc' = [alloc EXCEPT ![c] = {}]
  /\ req'   = [req   EXCEPT ![c] = {}]
  /\ UNCHANGED turn

(*
  Scheduler advances the head of the Round sequence.
*)
Schedule ==
  /\ turn' = IF turn < Len(Round) THEN turn + 1 ELSE 1
  /\ UNCHANGED << req, alloc >>

Next ==
  \/ \E c \in CLIENTS : IssueReq(c)
  \/ \E c \in CLIENTS : Allocate(c)
  \/ \E c \in CLIENTS : ReturnSome(c)
  \/ \E c \in CLIENTS : ReturnWhenSatisfied(c)
  \/ Schedule

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Schedule)
  /\ \A c \in CLIENTS : WF_vars(ReturnWhenSatisfied(c))
  /\ \A c \in CLIENTS : WF_vars(Allocate(c))

(*
  Safety invariants
*)
TypeInv ==
  /\ req \in [CLIENTS -> SUBSET RESOURCES]
  /\ alloc \in [CLIENTS -> SUBSET RESOURCES]
  /\ turn \in 1..Len(Round)

MutualExclusionInv ==
  \A c1, c2 \in CLIENTS : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

AllocatorInv ==
  /\ \A c \in CLIENTS : alloc[c] \subseteq req[c]
  /\ AllAllocated \subseteq RESOURCES
  /\ Available = RESOURCES \ AllAllocated

SafetyInv == TypeInv /\ MutualExclusionInv /\ AllocatorInv

(*
  Liveness properties (to be checked against Spec)
*)
EventuallyReturn ==
  \A c \in CLIENTS :
    [] ( (alloc[c] = req[c]) /\ alloc[c] # {} => <> (alloc[c] = {} /\ req[c] = {}) )

EventualSatisfaction ==
  \A c \in CLIENTS :
    [] ( req[c] # {} => <> (alloc[c] = req[c]) )

InfinitelyOftenSatisfied ==
  \A c \in CLIENTS : [] <> (alloc[c] = req[c])

=============================================================================