---------------------------- MODULE LamportFastMutex ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N, M
ASSUME N > 0 /\ M >= 0 /\ M < N

VARIABLE flag, fastPath, critical, trying

Init ==
  /\ flag = [i \in 1..N |-> FALSE]
  /\ fastPath = <<>>
  /\ critical = {}
  /\ trying = {}

Next ==
  \/ \E i \in 1..M : NextProcess(i)
  \/ \E i \in (M+1)..N : NextProcess(i)

NextProcess(self) ==
  IF self \in trying THEN
    IF fastPath = <<>> THEN
      /\ flag[self] := TRUE
      /\ fastPath := <<self>>
      /\ UNCHANGED critical
      /\ UNCHANGED trying
    ELSE
      /\ fastPath := Append(fastPath, self)
      /\ UNCHANGED flag
      /\ UNCHANGED critical
      /\ UNCHANGED trying
  ELSE
    IF self \in critical THEN
      /\ critical := critical \ {self}
      /\ trying := trying \ {self}
      /\ UNCHANGED flag
      /\ UNCHANGED fastPath
    ELSE
      /\ trying := trying \cup {self}
      /\ UNCHANGED flag
      /\ UNCHANGED fastPath
      /\ UNCHANGED critical

Spec ==
  /\ Init
  /\ [][Next]_flag
  /\ WF_vars(NextProcess)(1..M)
  /\ WF_vars(NextProcess)(M+1..N)

Invariant ==
  /\ flag \in [1..N -> BOOLEAN]
  /\ fastPath \in Seq(1..N)
  /\ critical \subseteq 1..N
  /\ trying \subseteq 1..N

Liveness ==
  <>[]<>(\E i \in 1..N : i \in critical)

THEOREM Spec => []Invariant
THEOREM Spec => Liveness
===============================================================================