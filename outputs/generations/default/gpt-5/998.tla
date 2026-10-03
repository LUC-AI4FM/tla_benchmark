------------------------------ MODULE ResourceAllocator ------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Clients,
  Resources,
  Schedule

ASSUME
  /\ Clients # {}
  /\ Resources # {}
  /\ Schedule \in Seq(Clients)
  /\ Len(Schedule) > 0

VARIABLES held, req, pos

Vars == << held, req, pos >>

Init ==
  /\ held = [c \in Clients |-> {}]
  /\ req  = [c \in Clients |-> {}]
  /\ pos  = 1

Cur() == Schedule[pos]

Free(r) == r \in Resources /\ \A c \in Clients : r \notin held[c]

RequestFor(c, R) ==
  /\ c \in Clients
  /\ R \in SUBSET Resources
  /\ R # {}
  /\ req[c] = {}
  /\ held[c] = {}
  /\ req' = [req EXCEPT ![c] = R]
  /\ UNCHANGED << held, pos >>

AllocateFor(c) ==
  /\ c \in Clients
  /\ c = Cur()
  /\ \E r \in (req[c] \ held[c]) :
        /\ Free(r)
        /\ held' = [held EXCEPT ![c] = @ \cup {r}]
  /\ UNCHANGED << req, pos >>

ReturnSomeFor(c, S) ==
  /\ c \in Clients
  /\ S \in SUBSET held[c]
  /\ S # {}
  /\ held' = [held EXCEPT ![c] = @ \ S]
  /\ UNCHANGED << req, pos >>

ReturnDoneFor(c) ==
  /\ c \in Clients
  /\ req[c] # {}
  /\ req[c] \subseteq held[c]
  /\ held[c] # {}
  /\ held' = [held EXCEPT ![c] = {}]
  /\ req'  = [req  EXCEPT ![c] = {}]
  /\ UNCHANGED pos

ScheduleStep ==
  /\ pos' = IF pos < Len(Schedule) THEN pos + 1 ELSE 1
  /\ UNCHANGED << held, req >>

RequestAct ==
  \E c \in Clients, R \in SUBSET Resources :
    /\ R # {}
    /\ RequestFor(c, R)

AllocateAct ==
  \E c \in Clients : AllocateFor(c)

ReturnSomeAct ==
  \E c \in Clients, S \in SUBSET held[c] :
    /\ S # {}
    /\ ReturnSomeFor(c, S)

ReturnDoneAct ==
  \E c \in Clients : ReturnDoneFor(c)

Next ==
  \/ RequestAct
  \/ AllocateAct
  \/ ReturnSomeAct
  \/ ReturnDoneAct
  \/ ScheduleStep

TypeInv ==
  /\ held \in [Clients -> SUBSET Resources]
  /\ req  \in [Clients -> SUBSET Resources]
  /\ pos \in 1..Len(Schedule)

MutexInv ==
  \A c1, c2 \in Clients : c1 # c2 => held[c1] \cap held[c2] = {}

AllocInv ==
  \A c \in Clients : held[c] \subseteq req[c]

NoHoldWithoutReq ==
  \A c \in Clients : req[c] = {} => held[c] = {}

SafeInv == TypeInv /\ MutexInv /\ AllocInv /\ NoHoldWithoutReq

Sat(c) == c \in Clients /\ req[c] # {} /\ req[c] \subseteq held[c]

EventuallyReturn(c) ==
  [] (Sat(c) => <> (req[c] = {} /\ held[c] = {}))

EventuallyObtain(c) ==
  [] (req[c] # {} => <> Sat(c))

InfOftenSatisfied(c) ==
  [] <> Sat(c)

AllEventuallyReturn ==
  \A c \in Clients : EventuallyReturn(c)

AllEventuallyObtain ==
  \A c \in Clients : EventuallyObtain(c)

AllInfOftenSatisfied ==
  \A c \in Clients : InfOftenSatisfied(c)

FairAllocate ==
  \A c \in Clients : WF_Vars(AllocateFor(c))

FairReturn ==
  \A c \in Clients : WF_Vars(ReturnDoneFor(c))

FairSchedule ==
  WF_Vars(ScheduleStep)

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ FairAllocate
  /\ FairReturn
  /\ FairSchedule

=============================================================================