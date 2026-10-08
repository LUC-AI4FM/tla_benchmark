```
MODULE Repository
EXTENDS Integers, FiniteSets

CONSTANTS Universe
VARIABLES repository

Init == repository = {}

Next == 
  /\ repository' = repository \cup {x}
  /\ x \in Universe

Spec == Init /\ [][Next]_repository

MonotonicityInvariant == repository \subseteq repository'

NoDuplicatesInvariant == repository \subseteq Universe

EmptyInitialInvariant == Init => repository = {}

ReachabilityInvariant == 
  repository \subseteq Universe
  /\ \A x \in repository : 
      \E s \in [Init .. Spec] : 
        s.repository = {} 
        /\ <><<s>>_repository \in [Next]_repository

EventualAdditionOfItem(x) == <><>repository \cap {x} /= {}

Fairness == \A x \in Universe : EventualAdditionOfItem(x)

SpecWithFairness == Spec /\ Fairness

THEOREM Spec => []NoDuplicatesInvariant
THEOREM Spec => []MonotonicityInvariant
THEOREM Spec => []EmptyInitialInvariant
THEOREM Spec => []ReachabilityInvariant
```