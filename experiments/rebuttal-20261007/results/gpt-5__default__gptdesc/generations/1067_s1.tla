-------------------------- MODULE RingTerminationDetection --------------------------

EXTENDS Naturals

CONSTANTS 
  Node, \* nonempty set of node identifiers
  Succ   \* ring successor function

ASSUME /\ Node # {}
       /\ Succ \in [Node -> Node]
       /\ IsBijection(Succ)

IsBijection(f) ==
  /\ f \in [Node -> Node]
  /\ \A x, y \in Node: f[x] = f[y] => x = y
  /\ \A y \in Node: \E x \in Node: f[x] = y

VARIABLES active, detected

vars == << active, detected >>

TypeInv ==
  /\ active \subseteq Node
  /\ detected \in BOOLEAN

AllInactive == active = {}

Init ==
  /\ TypeInv
  /\ detected = FALSE

Terminate(n) ==
  /\ n \in active
  /\ active' = active \ {n}
  /\ UNCHANGED detected

Wake(n) ==
  /\ n \in active
  /\ LET m == Succ[n]
     IN active' = active \cup {m}
  /\ UNCHANGED detected

Detect ==
  /\ AllInactive
  /\ ~detected
  /\ UNCHANGED active
  /\ detected' = TRUE

Next ==
  \/ (\E n \in active: Terminate(n))
  \/ (\E n \in active: Wake(n))
  \/ Detect

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Detect)

\* Safety invariants
CorrectnessInv == detected => AllInactive

\* Quiescence and liveness properties
PostDetectionQuiescence ==
  [](detected => []UNCHANGED vars)

QuiescenceLeadsToDetection ==
  (<>[]AllInactive) => (<>detected)

THEOREM Spec => []TypeInv
THEOREM Spec => []CorrectnessInv
THEOREM Spec => PostDetectionQuiescence
THEOREM Spec => QuiescenceLeadsToDetection

=============================================================================