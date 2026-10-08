--------------------------- MODULE SharedRegisters ---------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLES registers, localState, pc

registers == [i \in 1..N |-> {0}]
localState == [i \in 1..N |-> 0]
pc == [i \in 1..N |-> "start"]

Write(i, v) ==
  /\ pc[i] = "write"
  /\ registers' = [registers EXCEPT ![i] = registers[i] \cup {v}]
  /\ localState' = localState
  /\ pc' = [pc EXCEPT ![i] = "written"]
  /\ Unchanged << >>

CompleteWrite(i) ==
  /\ pc[i] = "written"
  /\ registers' = [registers EXCEPT ![i] = {v \in registers[i] : v /= 0}]
  /\ localState' = localState
  /\ pc' = [pc EXCEPT ![i] = "read"]
  /\ Unchanged << >>

Read(i) ==
  /\ pc[i] = "read"
  /\ \E v \in (registers[(i-1) % N + 1]) :
      localState' = [localState EXCEPT ![i] = v]
  /\ registers' = registers
  /\ pc' = [pc EXCEPT ![i] = "terminated"]
  /\ Unchanged << >>

Next ==
  \E i \in 1..N :
    (pc[i] = "start" /\ Write(i, 1))
    \/ CompleteWrite(i)
    \/ Read(i)

Spec == Initialize /\ [][Next]_<<registers, localState, pc>>

Initialize ==
  /\ registers = [i \in 1..N |-> {0}]
  /\ localState = [i \in 1..N |-> 0]
  /\ pc = [i \in 1..N |-> "start"]

PCorrect == <>(\A i \in 1..N : pc[i] = "terminated") => (\E i \in 1..N : localState[i] = 1)

TypeOK ==
  /\ registers \in [1..N -> SUBSET {0, 1}]
  /\ localState \in [1..N -> {0, 1}]
  /\ pc \in [1..N -> {"start", "write", "written", "read", "terminated"}]

Inv == TypeOK

THEOREM Spec => []PCorrect
THEOREM Spec => <><>(\A i \in 1..N : pc[i] = "terminated")
=============================================================================