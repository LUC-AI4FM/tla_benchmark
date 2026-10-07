---- MODULE ResourceAllocator ----
EXTENDS Naturals, Sequences

CONSTANTS
  Clients,      \* finite, nonempty set of clients
  Resources,    \* finite, nonempty set of resources
  SchedSeq      \* nonempty sequence over Clients constraining service order

ASSUME
  /\ Clients # {}
  /\ Resources # {}
  /\ SchedSeq \in Seq(Clients)
  /\ Len(SchedSeq) >= 1

VARIABLES
  req,   \* [Clients -> SUBSET Resources]: current requested set per client; {} means no outstanding request
  hold,  \* [Clients -> SUBSET Resources]: resources currently held per client
  pos    \* 1..Len(SchedSeq): current position in the schedule sequence

vars == << req, hold, pos >>

\* Helpers
SchedClient == SchedSeq[pos]

Need(c) == req[c] \ hold[c]

Available == Resources \ UNION { hold[c] : c \in Clients }

\* Initialization
Init ==
  /\ req = [c \in Clients |-> {}]
  /\ hold = [c \in Clients |-> {}]
  /\ pos = 1

\* Actions

RequestC(c) ==
  /\ c \in Clients
  /\ req[c] = {}
  /\ hold[c] = {}
  /\ \E R \in SUBSET Resources:
       /\ R # {}
       /\ req' = [req EXCEPT ![c] = R]
       /\ hold' = hold
       /\ pos' = pos

AllocateC(c) ==
  /\ c \in Clients
  /\ c = SchedClient
  /\ Need(c) # {}
  /\ LET ASet == Available \cap Need(c) IN
       /\ ASet # {}
       /\ \E A \in SUBSET ASet:
            /\ A # {}
            /\ hold' = [hold EXCEPT ![c] = @ \cup A]
            /\ req' = req
            /\ pos' = pos

ReturnSomeC(c) ==
  /\ c \in Clients
  /\ hold[c] # {}
  /\ \E A \in SUBSET hold[c]:
       /\ A # {}
       /\ hold' = [hold EXCEPT ![c] = @ \ A]
       /\ req' = req
       /\ pos' = pos

ReturnAllC(c) ==
  /\ c \in Clients
  /\ req[c] # {}
  /\ Need(c) = {}
  /\ req' = [req EXCEPT ![c] = {}]
  /\ hold' = [hold EXCEPT ![c] = {}]
  /\ pos' = pos

SchedStep ==
  /\ req' = req
  /\ hold' = hold
  /\ pos' = IF pos < Len(SchedSeq) THEN pos + 1 ELSE 1

Request == \E c \in Clients: RequestC(c)
Allocate == \E c \in Clients: AllocateC(c)
ReturnSome == \E c \in Clients: ReturnSomeC(c)
ReturnAll == \E c \in Clients: ReturnAllC(c)

Next ==
  Request
  \/ Allocate
  \/ ReturnSome
  \/ ReturnAll
  \/ SchedStep

\* Fairness (weak fairness)
Fairness ==
  /\ WF_vars(SchedStep)                                         \* scheduling eventually occurs
  /\ \A c \in Clients: WF_vars(AllocateC(c))                    \* allocations eventually happen when enabled
  /\ \A c \in Clients: WF_vars(ReturnAllC(c))                   \* once fully satisfied, clients eventually return

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety invariants

TypeInv ==
  /\ req \in [Clients -> SUBSET Resources]
  /\ hold \in [Clients -> SUBSET Resources]
  /\ pos \in 1..Len(SchedSeq)

MutEx == \A c1, c2 \in Clients : c1 # c2 => (hold[c1] \cap hold[c2]) = {}

HeldWithinRequest == \A c \in Clients : hold[c] \subseteq req[c]

AllocatorInv ==
  /\ UNION { hold[c] : c \in Clients } \subseteq Resources
  /\ HeldWithinRequest

AllSafetyInv == TypeInv /\ MutEx /\ AllocatorInv

\* Liveness properties

Satisfied(c) == req[c] # {} /\ Need(c) = {}

EventualReturn ==
  \A c \in Clients : []( Satisfied(c) => <> (req[c] = {} /\ hold[c] = {}) )

EventualObtainment ==
  \A c \in Clients : []( (req[c] # {}) => <> (Need(c) = {}) )

InfinitelyOftenSatisfied ==
  []<>( \E c \in Clients : Satisfied(c) )

====