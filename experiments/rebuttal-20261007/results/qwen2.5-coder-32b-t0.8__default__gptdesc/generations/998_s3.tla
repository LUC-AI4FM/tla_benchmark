----------------------------- MODULE ResourceAllocator -----------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    Clients,                \* A finite set of clients
    Resources               \* A finite set of resources

VARIABLES 
    held,                   \* [Clients -> SUBSET Resources] Resources currently held by each client
    requested,              \* [Clients -> SUBSET Resources] Resources currently requested by each client
    satisfied,              \* [Clients -> SUBSET Resources] Resources currently fully satisfied for each client
    schedule                \* A sequence of clients representing the order in which requests can be served

Init == 
    /\ held = [c \in Clients |-> {}]
    /\ requested = [c \in Clients |-> {}]
    /\ satisfied = [c \in Clients |-> {}]
    /\ schedule = <<>>

Next ==
    \/ \E c \in Clients : ~(/\ r \in Resources : r \notin requested[c])
                             /\ ~(\E r \in Resources : r \in held[c])
                             /\ \E i \in 1..Len(schedule) : schedule[i] = c
                             /\ /\ [][r \in requested[schedule[i]] \ {r' \in requested[schedule[i]] : r' \in held[schedule[i]]} |->
                                    \E s \in SUBSET Resources \ (held[schedule[i]] \cup satisfied[schedule[i]]) :
                                        \/ r \notin s
                                        \/ /\ r \in s
                                           /\ r \notin union {held[c'] | c' \in Clients}
                                           /\ ~(\E c' \in Clients : c' \in schedule /\ requested[c'][r])
                             => /\ held' = [h \in held EXCEPT ![schedule[i]] = held[schedule[i]] \cup {r}]
                                 /\ satisfied' = [s \in satisfied EXCEPT ![schedule[i]] = satisfied[schedule[i]] \cup {r}]
    \/ \E c \in Clients : \A r \in requested[c] : r \in satisfied[c]
                          => /\ requested' = [req \in requested EXCEPT ![c] = {}]
                              /\ schedule' = <<c>>
    \/ \E i, j \in 1..Len(schedule) : i < j
                             /\ \A c \in Clients : ~(/\ r \in Resources : r \notin requested[c])
                                                   /\ ~(\E r \in Resources : r \in held[c])
                                                   /\ ~(\E k \in 1..i : schedule[k] = c)
                             => schedule' = Append(SubSeq(schedule, 1, i - 1),
                                                  SubSeq(schedule, j + 1, Len(schedule)))

Spec ==
    /\ Init
    /\ [][Next]_<<held, requested, satisfied, schedule>>

SafetyInvariant ==
    /\ \A c \in Clients : satisfied[c] \subseteq requested[c]
    /\ \A r \in Resources : Cardinality({c \in Clients : r \in held[c]}) <= 1

LivenessReturn ==
    WF_vars_<<schedule>>[Next]
    /\ SF_vars_<<schedule>>[\E c \in Clients : \A r \in requested[c] : r \in satisfied[c]]

LivenessAllocation ==
    WF_vars_<<schedule>>[Next]
    /\ SF_vars_<<schedule>>[\E i \in 1..Len(schedule) :
        \E [r \in requested[schedule[i]] \ {r' \in requested[schedule[i]] : r' \in held[schedule[i]]}] :
            /\ r \notin union {held[c'] | c' \in Clients}
            /\ ~(\E c' \in Clients : c' \in schedule /\ requested[c'][r])]

LivenessScheduling ==
    WF_vars_<<schedule>>[Next]
    /\ SF_vars_<<schedule>>[\A c \in Clients :
        ~(/\ r \in Resources : r \notin requested[c])
        /\ ~(\E r \in Resources : r \in held[c])
        => \E i \in 1..Len(schedule) : schedule[i] = c]

LivenessObtainment ==
    WF_vars_<<schedule>>[Next]
    /\ SF_vars_<<schedule>>[\A c \in Clients :
        ~(/\ r \in Resources : r \notin requested[c])
        /\ ~(\E r \in Resources : r \in held[c])
        => \E i \in 1..Len(schedule) :
            \E [r \in requested[schedule[i]] \ {r' \in requested[schedule[i]] : r' \in held[schedule[i]]}] :
                /\ r \notin union {held[c'] | c' \in Clients}
                /\ ~(\E c' \in Clients : c' \in schedule /\ requested[c'][r])]

LivenessSatisfied ==
    WF_vars_<<schedule>>[Next]
    /\ SF_vars_<<schedule>>[\A c \in Clients :
        \E i, j \in 1..Len(schedule) : i < j
        /\ \A c' \in Clients : ~(/\ r \in Resources : r \notin requested[c'])
                              /\ ~(\E r \in Resources : r \in held[c'])
                              /\ ~(\E k \in 1..i : schedule[k] = c')
        => \E r \in requested[c] : r \in satisfied[c]]

=============================================================================