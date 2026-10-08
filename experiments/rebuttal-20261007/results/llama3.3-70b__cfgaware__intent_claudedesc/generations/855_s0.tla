---------------------------- MODULE SwitchPuzzle ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Prisoner
VARIABLE p2, p3, switch1, switch2, visited, count

Spec == 
  /\ switch1 \in {0, 1}
  /\ switch2 \in {0, 1}
  /\ visited \in SUBSET Prisoner
  /\ count \in 0..Cardinality(Prisoner)
  /\ [][
      /\ \A p \in Prisoner : 
        <>\[p = p2 /\ switch1' = 1 - switch1 /\ switch2' = switch2 
           \/ p /= p2 /\ (switch1' = 1 - switch1 /\ switch2' = switch2 
                       \/ switch1' = switch1 /\ switch2' = 1 - switch2)
           /\ IF p = p2 THEN visited' = visited \cup {p} ELSE visited' = visited
           /\ count' = IF p = p2 THEN count + 1 ELSE count
        ]_
      /\ count' = count
      /\ UNCHANGED <<switch1, switch2, visited>>
    ]
  /\ WF_(p \in Prisoner) ([][
      /\ \A p \in Prisoner : 
        <>\[p = p2 /\ switch1' = 1 - switch1 /\ switch2' = switch2 
           \/ p /= p2 /\ (switch1' = 1 - switch1 /\ switch2' = switch2 
                       \/ switch1' = switch1 /\ switch2' = 1 - switch2)
           /\ IF p = p2 THEN visited' = visited \cup {p} ELSE visited' = visited
           /\ count' = IF p = p2 THEN count + 1 ELSE count
        ]_
      /\ count' = count
      /\ UNCHANGED <<switch1, switch2, visited>>
    ])

TypeOK == 
  /\ switch1 \in {0, 1}
  /\ switch2 \in {0, 1}
  /\ visited \subseteq Prisoner
  /\ count \in 0..Cardinality(Prisoner)

CountInvariant == 
  /\ TypeOK
  /\ (count = Cardinality(visited))

Safety == 
  []\[count = Cardinality(Prisoner) => visited = Prisoner]

Liveness == 
  <>\[count = Cardinality(Prisoner)]

THEOREM Spec => []TypeOK
THEOREM Spec => CountInvariant
THEOREM Spec => Safety
THEOREM Spec => Liveness
=============================================================================