---- MODULE ResourceAllocator ----

CONSTANTS Clients, Resources

VARIABLES unsat, alloc, sched

ASSUME Cardinality(Clients) = 3 /\ Cardinality(Resources) = 2

Request ==
    \E c \in Clients : 
        \E r \subseteq Resources :
            r /= {} /\ unsat[c] = {} /\ alloc[c] = {} /\
            /\ 'unsat' = [unsat EXCEPT ![c] = r]

Schedule ==
    LET pendingClients == {c \in Clients | unsat[c] /= {}}
        permutedPendingClients == PERMUTATIONS(pendingClients)
    IN
        \E p \in permutedPendingClients :
            /\ 'sched' = Append(sched, SeqFromSet(p))

Allocate ==
    \E c \in DOMAIN sched :
        LET availableResources == Resources \ (DOMAIN alloc) 
            requestedResources == unsat[sched[c]]
            grantedResources == requestedResources \cap availableResources
        IN
            grantedResources /= {} /\
            /\ 'alloc' = [alloc EXCEPT ![sched[c]] = (alloc[sched[c]] \cup grantedResources)]
            /\ IF grantedResources = requestedResources THEN
                'unsat' = [unsat EXCEPT ![sched[c]] = {}]
               ELSE
                UNCHANGED unsat
            /\ 'sched' = Tail(sched)

Return ==
    \E c \in Clients :
        \E r \subseteq alloc[c] :
            r /= {} /\
            /\ 'alloc' = [alloc EXCEPT ![c] = (alloc[c] \ r)]

Next == Request \/ Schedule \/ Allocate \/ Return

Spec == 
    VARIABLES unsat, alloc, sched
    INIT
        /\ unsat = [c \in Clients |-> {}]
        /\ alloc = [c \in Clients |-> {}]
        /\ sched = << >>
    NEXT Next

TypeOK ==
    /\ unsat \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]
    /\ sched \in Seq(Clients)

MutualExclusion ==
    \A r \in Resources :
        Cardinality({c \in Clients | r \in alloc[c]}) <= 1

Schedulability ==
    \A c \in Clients :
        unsat[c] /= {} => c \in DOMAIN sched

ReturnFairness ==
    WF_vars(Next, {s \in S_ : \E c \in Clients : alloc[c] = Resources} -> Return)

AllocateFairness ==
    WF_vars(Next, {s \in S_ : \E c \in Clients : unsat[c] /= {}} -> Allocate)

ScheduleFairness ==
    WF_vars(Next, {s \in S_ : \E c \in Clients : unsat[c] /= {} /\ c \notin DOMAIN sched} -> Schedule)

THEOREM TypeOK
THEOREM MutualExclusion
THEOREM Schedulability
THEOREM ReturnFairness
THEOREM AllocateFairness
THEOREM ScheduleFairness

====