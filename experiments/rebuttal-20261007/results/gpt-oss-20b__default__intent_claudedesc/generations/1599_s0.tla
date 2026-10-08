MODULE LamportFastMutex
\*======================================================================
\*  Mutual exclusion algorithm (Lamport's fast mutex) for N processes.
\*======================================================================

CONSTANT N \* Number of processes (positive integer)

VARIABLES state, flag, X, Y

(*--------------------------------------------------------------------
   Type definitions and derived predicates
--------------------------------------------------------------------*)
StateVal == {"NonCritical", "Trying1", "Trying2", "Critical"}

InCS(i)      == state[i] = "Critical"
Attempting(i)== state[i] = "Trying1" \/ state[i] = "Trying2"

(*--------------------------------------------------------------------
   Initial condition
--------------------------------------------------------------------*)
Init ==
  /\ X = 0
  /\ Y = 0
  /\ \A i ∈ 1..N : flag[i] = FALSE
  /\ \A i ∈ 1..N : state[i] = "NonCritical"

(*--------------------------------------------------------------------
   Actions for process i
--------------------------------------------------------------------*)
TryEnter1(i) ==
  /\ state[i] = "NonCritical"
  /\ state' = [state EXCEPT ![i] = "Trying1"]
  /\ flag'  = [flag  EXCEPT ![i] = TRUE]
  /\ X'     = i
  /\ UNCHANGED <<Y>>

TryEnter2(i) ==
  /\ state[i] = "Trying1"
  /\ Y = 0
  /\ state' = [state EXCEPT ![i] = "Trying2"]
  /\ Y'     = i
  /\ UNCHANGED <<X, flag>>

TryExitIfCont(i) ==
  /\ state[i] = "Trying1"
  /\ Y # 0
  /\ state' = [state EXCEPT ![i] = "NonCritical"]
  /\ flag'  = [flag  EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<X, Y>>

TryEnterCS(i) ==
  /\ state[i] = "Trying2"
  /\ X = i
  /\ state' = [state EXCEPT ![i] = "Critical"]
  /\ UNCHANGED <<flag, X, Y>>

TryExitIfCont2(i) ==
  /\ state[i] = "Trying2"
  /\ X # i
  /\ state' = [state EXCEPT ![i] = "NonCritical"]
  /\ flag'  = [flag  EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<X, Y>>

LeaveCS(i) ==
  /\ state[i] = "Critical"
  /\ state' = [state EXCEPT ![i] = "NonCritical"]
  /\ flag'  = [flag  EXCEPT ![i] = FALSE]
  /\ Y'     = 0
  /\ UNCHANGED <<X>>

(*--------------------------------------------------------------------
   Next-state relation
--------------------------------------------------------------------*)
Next ==
  \E i ∈ 1..N :
    ( TryEnter1(i) \/ TryEnter2(i) \/ TryExitIfCont(i)
      \/ TryEnterCS(i) \/ TryExitIfCont2(i) \/ LeaveCS(i) )

(*--------------------------------------------------------------------
   Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(*--------------------------------------------------------------------
   Safety invariant: mutual exclusion
--------------------------------------------------------------------*)
MutualExcl ==
  \A i, j ∈ 1..N : ~(InCS(i) /\ InCS(j))

(*--------------------------------------------------------------------
   Conditional liveness property
--------------------------------------------------------------------*)
CondLiveness ==
  \A i ∈ 1..N :
    ([]Attempting(i) => []<>(\E j ∈ 1..N : InCS(j)))

(*======================================================================
   End of module
======================================================================*)