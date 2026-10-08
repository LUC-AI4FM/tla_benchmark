```
MODULE ResourceAllocator
EXTENDS Integers, FiniteSets

CONSTANTS Resources, Clients
VARIABLES requested, held, returned

Init ==
  /\ requested \in [Clients -> SUBSET Resources]
  /\ held \in [Clients -> SUBSET Resources]
  /\ returned \in [Clients -> SUBSET Resources]
  /\ requested = [c \in Clients |-> {}]
  /\ held = [c \in Clients |-> {}]
  /\ returned = [c \in Clients |-> {}]

Next ==
  /\ (requested' = requested) 
     ∨ (\E c \in Clients : 
          /\ requested[c] = {}
          /\ held[c] = {}
          /\ requested' = [requested EXCEPT ![c] = some r \in Resources]
       )
  ∨ (\E c \in Clients, r \in Resources :
        /\ r \in requested[c]
        /\ r \notin held[c]
        /\ held' = [held EXCEPT ![c] = held[c] \cup {r}]
        /\ requested' = requested
        /\ returned' = returned
     )
  ∨ (\E c \in Clients, r \in Resources :
        /\ r \in held[c]
        /\ held' = [held EXCEPT ![c] = held[c] \ {r}]
        /\ requested' = requested
        /\ returned' = [returned EXCEPT ![c] = returned[c] \cup {r}]
     )

Spec == Init /\ [][Next]_<<requested, held, returned>>

THEOREM Spec => []TypeCorrectness
TypeCorrectness == 
  /\ requested \in [Clients -> SUBSET Resources]
  /\ held \in [Clients -> SUBSET Resources]
  /\ returned \in [Clients -> SUBSET Resources]

THEOREM Spec => []MutualExclusion
MutualExclusion ==
  \A c1, c2 \in Clients, r \in Resources :
    (r \in held[c1]) /\ (r \in held[c2]) => c1 = c2

THEOREM Spec => <>[]EventualReturn
EventualReturn == 
  \A c \in Clients : held[c] = {}

THEOREM Spec => WF_Var(Next)
WF_Var(Next) == <><<requested, held, returned>> 

THEOREM Spec => []<>NoUnsatisfiedRequests
NoUnsatisfiedRequests ==
  \A c \in Clients : requested[c] = {} \/ held[c] \cup returned[c] = requested[c]

Symmetry == <<c1, c2 \in Clients |-> {<<r1, r2 \in Resources |-> 
  /\ (requested'[c1] = requested'[c2]) 
  /\ (held'[c1] = held'[c2])
  /\ (returned'[c1] = returned'[c2])>>}>>

CounterExample == <<Resources = {1, 2}, Clients = {1, 2},
                    requested = [1 |-> {}, 2 |-> {}],
                    held = [1 |-> {}, 2 |-> {}],
                    returned = [1 |-> {}, 2 |-> {}]>>
```