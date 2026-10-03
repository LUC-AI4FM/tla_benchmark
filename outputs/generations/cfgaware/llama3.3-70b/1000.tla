---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Resources, Clients
VARIABLES clientResources, pendingRequests, returnedResources

TypeCorrectness == 
  /\ clientResources \in [Clients -> SUBSET Resources]
  /\ pendingRequests \in [Clients -> SUBSET Resources]
  /\ returnedResources \in [Clients -> SUBSET Resources]

MutualExclusion == 
  \A c1, c2 \in Clients : c1 # c2 => clientResources[c1] \cap clientResources[c2] = {}

EventualReturn == 
  \A c \in Clients : 
    <<c>>_returnedResources \in FairnessWeak(
      \E r \in Resources : r \in returnedResources[c]
    )

EventualObtainment == 
  \A c \in Clients, r \in Resources :
    <<c, r>>_pendingRequests \in FairnessStrong(
      r \in clientResources[c]
    )

InfinitelyOftenNoUnsatisfiedRequests == 
  \A c \in Clients : 
    <<c>>_noUnsatisfiedRequests \in InfinitelyOften(
      pendingRequests[c] = {}
    )

SymmetryExpression == 
  (Clients \* Resources)

CounterexampleValueStructure == 
  [ type => "counterexample", 
    clientResources => <<1, 2>>, 
    pendingRequests => <<3, 4>>, 
    returnedResources => <<5, 6>> ]

NoUnsatisfiedRequests(c) == pendingRequests[c] = {}

RequestStep(c, r) == 
  /\ c \in Clients
  /\ r \in Resources
  /\ clientResources' = [clientResources EXCEPT ![c] = clientResources[c] \cup {r}]
  /\ pendingRequests' = [pendingRequests EXCEPT ![c] = pendingRequests[c] \ {r}]
  /\ returnedResources' = returnedResources

ReturnStep(c, r) == 
  /\ c \in Clients
  /\ r \in Resources
  /\ clientResources' = [clientResources EXCEPT ![c] = clientResources[c] \ {r}]
  /\ pendingRequests' = pendingRequests
  /\ returnedResources' = [returnedResources EXCEPT ![c] = returnedResources[c] \cup {r}]

Next == 
  \E c \in Clients, r \in Resources : 
    (RequestStep(c, r)) \/ (ReturnStep(c, r))

SpecWeakFairness == 
  Spec == Init /\ [][Next]_clientResources /\ [][Next]_pendingRequests /\ [][Next]_returnedResources
  FairnessWeak == EventualReturn /\ EventualObtainment

SpecStrongFairness == 
  Spec == Init /\ [][Next]_clientResources /\ [][Next]_pendingRequests /\ [][Next]_returnedResources
  FairnessStrong == InfinitelyOftenNoUnsatisfiedRequests

THEOREM SpecWeakFairness => []TypeCorrectness
THEOREM SpecWeakFairness => []MutualExclusion
THEOREM SpecStrongFairness => <>[]NoUnsatisfiedRequests(c)

=============================================================================