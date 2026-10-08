--------------------------- MODULE FastMutex ----------------------------
EXTENDS Naturals, Sequences, TLC, SETS

CONSTANT N \* Number of processes

VARIABLES x, y, b, state, cs

vars == <<x, y, b, state, cs>>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 1..N |-> FALSE]
  /\ state = [i \in 1..N |-> "idle"]
  /\ cs = {}

IdleTry(i) ==
  /\ state[i] = "idle"
  /\ x' = i
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ state' = [state EXCEPT ![i] = "waitFast"]
  /\ UNCHANGED <<y, cs>>

WaitFastToCritical(i) ==
  /\ state[i] = "waitFast"
  /\ (y = 0 \/ x = i)
  /\ cs' = cs \cup {i}
  /\ state' = [state EXCEPT ![i] = "critical"]
  /\ UNCHANGED <<x, y, b>>

PrepareSlow(i) ==
  /\ state[i] = "waitFast"
  /\ ~(y = 0 \/ x = i)
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ y' = i
  /\ state' = [state EXCEPT ![i] = "waitSlow"]
  /\ UNCHANGED <<x, cs>>

WaitSlowToCritical(i) ==
  /\ state[i] = "waitSlow"
  /\ (x = i)
  /\ cs' = cs \cup {i}
  /\ state' = [state EXCEPT ![i] = "critical"]
  /\ UNCHANGED <<x, y, b>>

ExitCS(i) ==
  /\ state[i] = "critical"
  /\ cs' = cs \ {i}
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ state' = [state EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<x, y>>

ProcAction(i) ==
  IdleTry(i) \/ WaitFastToCritical(i) \/ PrepareSlow(i) \/ WaitSlowToCritical(i) \/ ExitCS(i)

Next == \E i \in 1..N : ProcAction(i)

Spec == Init /\ [][Next]_vars
          /\ \A i \in 1..N : WF_action(ProcAction(i))

MutualExclusion == (#cs <= 1)
LivenessProperty == \E i \in 1..N : []<>(i \in cs)

=============================================================================