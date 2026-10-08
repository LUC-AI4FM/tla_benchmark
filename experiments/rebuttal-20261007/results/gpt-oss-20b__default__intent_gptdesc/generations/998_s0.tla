------------------------------ MODULE CentralAllocator ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS CLIENTS, RESOURCES

VARIABLES held, requested, schedule

(* Helper functions *)
SetOfSeq(s) == {x | x ∈ s}
IndexInSchedule(e) == CHOOSE i \in 1..Len(schedule) : schedule[i] = e
EarlierClients(c) == {p \in CLIENTS | p \in schedule /\ IndexInSchedule(p) < IndexInSchedule(c)}
AllHeld == UNION {held[c] : c \in CLIENTS}

vars == <<held, requested, schedule>>

(* Initial state *)
Init ==
    held \in [CLIENTS -> SUBSET RESOURCES] /\
    requested \in [CLIENTS -> SUBSET RESOURCES] /\
    schedule \in Seq(CLIENTS) /\
    /\ ∀ c \in CLIENTS : held[c] = {} /\ requested[c] = {} /\ 
    /\ schedule = <<>>

(* Actions *)
IssueRequest(c, R) ==
    /\ c \in CLIENTS
    /\ R \subseteq RESOURCES
    /\ requested[c] = {}
    /\ held[c] = {}
    /\ requested' = [requested EXCEPT ![c] = R]
    /\ UNCHANGED <<held, schedule>>

AllocateStep(c, r) ==
    /\ c \in CLIENTS
    /\ r \in RESOURCES
    /\ r \in requested[c]
    /\ r \notin AllHeld
    /\ c \in schedule
    /\ ∀ p \in EarlierClients(c) : r \notin requested[p]
    /\ requested' = [requested EXCEPT ![c] = requested[c] \ {r}]
    /\ held' = [held EXCEPT ![c] = held[c] \cup {r}]
    /\ UNCHANGED schedule

ReturnStep(c, r) ==
    /\ c \in CLIENTS
    /\ r \in held[c]
    /\ held' = [held EXCEPT ![c] = held[c] \ {r}]
    /\ UNCHANGED <<requested, schedule>>

ExtendSchedule ==
    /\ schedule' \in {s \in Seq(CLIENTS) |
           SetOfSeq(s) = {c \in CLIENTS | requested[c] # {} } /\
           Distinct(s)}
    /\ UNCHANGED <<held, requested>>

Next == IssueRequest(c, R) \/ AllocateStep(c, r) \/ ReturnStep(c, r) \/ ExtendSchedule

(* Invariants *)
MutualExclusion ==
    ∀ c1, c2 \in CLIENTS : c1 # c2 => held[c1] # held[c2]

NoEarlierRequestHold ==
    ∀ i, j \in 1..Len(schedule) :
        i < j =>
            ∀ r \in held[schedule[j]] : r \notin requested[schedule[i]]

ScheduledClientsHaveRequests ==
    ∀ i \in 1..Len(schedule) : requested[schedule[i]] # {}

ScheduleCorrect ==
    SetOfSeq(schedule) = {c \in CLIENTS | requested[c] # {} } /\ Distinct(schedule)

Safety == MutualExclusion /\ NoEarlierRequestHold /\ ScheduledClientsHaveRequests

(* Liveness properties *)
ClientReturn ==
    ∀ c \in CLIENTS : [] (requested[c] = {} => <> (held[c] = {}))

AllocationProgress == WF(AllocateStep)

ScheduleProgress ==
    WF(ExtendSchedule) /\
    ∀ c \in CLIENTS : [] (requested[c] # {} => <> (c \in schedule))

Feasibility ==
    ∀ c \in CLIENTS :
        c \in schedule =>
            ∀ r \in requested[c] :
                <> (r \notin AllHeld /\ 
                    ∀ p \in EarlierClients(c) : r \notin requested[p])

AllocAll ==
    ∀ c \in CLIENTS : [] (requested[c] # {} => <> (requested[c] = {}))

Spec == Init /\ [][Next]_vars /\ AllocationProgress /\ ScheduleProgress /\ ClientReturn /\ Feasibility /\ AllocAll

=============================================================================