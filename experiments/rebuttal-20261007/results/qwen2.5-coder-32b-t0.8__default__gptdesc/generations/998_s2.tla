------------------------------- MODULE ResourceAllocator -------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Clients, Resources, Schedule
ASSUME /\ Clients \subseteq Int
       /\ Resources \subseteq Int
       /\ Schedule \in Seq(Client -> Bool)

VARIABLES requests, allocations, heldResources

Init == 
  /\ requests = [c \in Clients |-> {}]
  /\ allocations = [r \in Resources |-> <<>>]
  /\ heldResources = [c \in Clients |-> {}]

Next ==
  \/ \E c \in Clients : 
       (\A r \in Resources : allocations[r] = <<>>)
       /\ requests[c] = {}
       /\ heldResources[c] = {}
       /\ /\E s \in SUBSEQ(Schedule) :
            Len(s) > 0
            /\ s[1][c]
          \/ (\A s \in SUBSEQ(Schedule) : Len(s) > 0 => ~s[1][c])
       /\ \/ \E r \in Resources \ (requests[c] \cup UNION {allocations[r]}):
              requests' = [requests EXCEPT ![c] = requests[c] \cup {r}]
          \/ requests' = requests
     \/ \E r \in Resources, c \in Clients :
        allocations[r] # <<>>
        /\ \A i \in 1..Len(allocations[r]) :
           allocations[r][i] \notin heldResources[allocations[r][i]]
        /\ (c \notin DOMAIN allocations[r])
        /\ requests[c] = {}
        /\ \/ \E i \in 1..Len(allocations[r]):
               c = allocations[r][i]
               /\ allocations' = [allocations EXCEPT ![r] = Tail(allocations[r])]
          \/ allocations' = allocations
     \/ \E r \in Resources, c \in Clients :
        c \notin DOMAIN allocations[r]
        /\ requests[c] # {}
        /\ heldResources[c] = {}
        /\ (\A s \in SUBSEQ(Schedule) : Len(s) > 0 => s[1][c])
        /\ \/ requests[c] \cap UNION {allocations[r']} = {}
               /\ r \notin UNION {allocations[r']}
            \/ \E r' \in Resources :
               requests[c] \cap allocations[r'] # {} 
               /\ r' = r
        /\ allocations'[r] = Append(allocations[r], c)
        /\ allocations'' = [allocations' EXCEPT ![r] = allocations'[r]]
        /\ requests'[c] = requests[c] \ {r}
        /\ requests'' = [requests' EXCEPT ![c] = requests'[c]]
     \/ \E c \in Clients :
        requests[c] = {}
        /\ heldResources[c] # {}
        /\ (\A s \in SUBSEQ(Schedule) : Len(s) > 0 => ~s[1][c])
        /\ \E r \in heldResources[c]:
           allocations[r]' = <<>>
        /\ allocations'' = [allocations' EXCEPT ![r] = allocations'[r]]
        /\ heldResources'[c] = {}
        /\ heldResources'' = [heldResources' EXCEPT ![c] = heldResources'[c]]

Spec ==
  Init /\ [][Next]_<<requests, allocations, heldResources>> 
      /\ WF_next(<<requests, allocations, heldResources>>) 

TypeInv == 
  /\ \A c \in Clients : requests[c] \subseteq Resources
  /\ \A r \in Resources : allocations[r] \in Seq(Clients)
  /\ \A c \in Clients : heldResources[c] \subseteq Resources

MutualExclusion ==
  \A r \in Resources, i \in 1..Len(allocations[r]) :
    \A j \in 1..Len(allocations[r]) :
      i # j => allocations[r][i] # allocations[r][j]

AllocatorInv ==
  \A c \in Clients : requests[c] = {} \/ heldResources[c] = {}

EventualReturn ==
  []<>[](\E r \in Resources, c \in Clients :
          allocations[r]' = <<>> /\ heldResources'[c] = {})

EventualObtainment ==
  []<>[](\E c \in Clients :
          requests[c] = {} /\ heldResources'[c] # {})

InfinitelyOftenSatisfied ==
  []<>(\A c \in Clients : 
        (\E r \in Resources, i \in 1..Len(allocations[r]) :
         allocations[r][i] = c) => requests[c]' = {})

Properties ==
  TypeInv /\ MutualExclusion /\ AllocatorInv
          /\ EventualReturn /\ EventualObtainment /\ InfinitelyOftenSatisfied

=============================================================================