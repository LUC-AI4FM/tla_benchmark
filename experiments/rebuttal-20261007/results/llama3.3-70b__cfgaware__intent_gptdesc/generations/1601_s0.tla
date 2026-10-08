--------------------------- MODULE FischerProtocol ---------------------------
EXTENDS Integers, FiniteSets

CONSTANT N, Epsilon, Delta
ASSUME Epsilon < Delta

VARIABLES timer, critical, memory, trying

Init ==
  /\ timer = [i \in 1..N |-> "inf"]
  /\ critical = {}
  /\ memory = << >>
  /\ trying = {}

Next ==
  \/ (\E i \in 1..N : 
        /\ trying' = trying \cup {i}
        /\ UNCHANGED <<timer, critical, memory>>)
  \/ (\E i \in 1..N :
        /\ trying = trying'
        /\ timer[i] = "inf"
        /\ memory = << >>
        /\ memory' = <<i>>
        /\ UNCHANGED <<critical, trying>>)
  \/ (\E i \in 1..N :
        /\ trying = trying'
        /\ timer[i] = "inf"
        /\ memory = <<i>>
        /\ timer' = [timer EXCEPT ![i] = Delta]
        /\ UNCHANGED <<critical, memory>>)
  \/ (\E i \in 1..N :
        /\ trying = trying'
        /\ timer[i] = Delta
        /\ memory = <<i>>
        /\ critical' = critical \cup {i}
        /\ timer' = [timer EXCEPT ![i] = "inf"]
        /\ UNCHANGED memory)
  \/ (\E i \in 1..N :
        /\ trying = trying'
        /\ critical = critical \cup {i}
        /\ critical' = critical \ {i}
        /\ memory' = << >>
        /\ timer' = [timer EXCEPT ![i] = "inf"]
        /\ UNCHANGED trying)
  \/ (\A i \in 1..N : 
        /\ timer[i] # "inf"
        /\ timer' = [timer EXCEPT ![i] = timer[i] - 1]
        /\ UNCHANGED <<critical, memory, trying>>)

Spec == Init /\ [][Next]_<<timer, critical, memory, trying>>

Invariant ==
  /\ critical \subseteq 1..N
  /\ Card(critical) <= 1
  /\ memory \in [1..N \cup {<< >>}]
  /\ timer \in [1..N -> {"inf"} \cup (0..Delta)]

Liveness == 
  /\ SF_VARIABLES(trying, timer, critical, memory)
  /\ (\A i \in 1..N : WF_VARIABLES(Next, trying, timer, critical, memory))
  /\ WF_<<tick>>(Next)

THEOREM Spec => []Invariant
THEOREM Spec => Liveness

=============================================================================