----------------------------- MODULE ResourceAllocator -----------------------------

EXTENDS Naturals, Sequences

CONSTANTS Clients, Resources, Schedule

VARIABLES want, hold, idx

vars == << want, hold, idx >>

AllHeld == UNION { hold[c] : c \in Clients }
Free == Resources \ AllHeld

TypeOK ==
  /\ want \in [Clients -> SUBSET Resources]
  /\ hold \in [Clients -> SUBSET Resources]
  /\ idx \in 1..Len(Schedule)
  /\ Schedule \in Seq(Clients)
  /\ Len(Schedule) >= 1

MutualExclusion ==
  \A c1, c2 \in Clients : c1 /= c2 => hold[c1] \cap hold[c2] = {}

AllocatorInv ==
  /\ TypeOK
  /\ MutualExclusion
  /\ AllHeld \subseteq Resources

Init ==
  /\ want = [ c \in Clients |-> {} ]
  /\ hold = [ c \in Clients |-> {} ]
  /\ idx = 1

Request(c) ==
  /\ c \in Clients
  /\ hold[c] = {}
  /\ want[c] = {}
  /\ \E w \in (SUBSET Resources) \ {{}} :
       want' = [want EXCEPT ![c] = w]
  /\ UNCHANGED << hold, idx >>

Allocate(c) ==
  /\ c \in Clients
  /\ c = Schedule[idx]
  /\ \E r \in (want[c] \ hold[c]) :
       /\ r \in Free
       /\ hold' = [hold EXCEPT ![c] = @ \cup {r}]
  /\ UNCHANGED << want, idx >>

ReturnSome(c) ==
  /\ c \in Clients
  /\ hold[c] # {}  \* allow early return of any nonempty subset
  /\ \E ret \in SUBSET hold[c] :
       /\ ret # {}
       /\ hold' = [hold EXCEPT ![c] = @ \ ret]
  /\ UNCHANGED << want, idx >>

ReturnAll(c) ==
  /\ c \in Clients
  /\ want[c] \subseteq hold[c]
  /\ hold[c] # {}
  /\ hold' = [hold EXCEPT ![c] = {}]
  /\ want' = [want EXCEPT ![c] = {}]
  /\ UNCHANGED idx

ScheduleStep ==
  /\ idx' = IF idx = Len(Schedule) THEN 1 ELSE idx + 1
  /\ UNCHANGED << want, hold >>

Next ==
  \/ \E c \in Clients : Request(c)
  \/ \E c \in Clients : Allocate(c)
  \/ \E c \in Clients : ReturnSome(c)
  \/ \E c \in Clients : ReturnAll(c)
  \/ ScheduleStep

Fairness ==
  /\ \A c \in Clients : WF_vars(Allocate(c))
  /\ \A c \in Clients : WF_vars(ReturnAll(c))
  /\ WF_vars(ScheduleStep)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

Liveness_EventualReturn ==
  \A c \in Clients :
    []( (want[c] \subseteq hold[c]) /\ (want[c] /= {}) => <> (hold[c] = {} /\ want[c] = {}) )

Liveness_EventualSatisfaction ==
  \A c \in Clients :
    []( want[c] /= {} => <> (want[c] \subseteq hold[c]) )

Liveness_InfOftenSatisfied ==
  \A c \in Clients :
    []<>( (want[c] = {}) \/ (want[c] \subseteq hold[c]) )

=============================================================================