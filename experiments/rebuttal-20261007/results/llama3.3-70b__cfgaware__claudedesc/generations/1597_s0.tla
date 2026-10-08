---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE x, y, b, failed, j, j2, cs

x == 0
y == 0
b == [i \in 1..N |-> FALSE]
failed == [i \in 1..N |-> FALSE]
j == 0
j2 == 0
cs == [i \in 1..N |-> FALSE]

Proc1 == 
  (* Set b flag *)
  /\ b' = [b EXCEPT ![1] = TRUE]
  /\ x' = 1
  /\ y' = y
  /\ failed' = failed
  /\ j' = j
  /\ j2' = j2
  /\ cs' = cs
  (* Check y *)
  \/ (y = 0 /\ 
      (* Write y and check x *)
      /\ y' = 1
      /\ x' = x
      /\ b' = b
      /\ failed' = failed
      /\ j' = j
      /\ j2' = j2
      /\ cs' = cs)
  \/ (y # 0 /\ 
      (* Back off and wait for y to clear *)
      /\ b' = b
      /\ x' = x
      /\ y' = y
      /\ failed' = failed
      /\ j' = j
      /\ j2' = j2
      /\ cs' = cs)

Proc2(i \in 2..N) == 
  (* Set b flag *)
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ x' = i
  /\ y' = y
  /\ failed' = failed
  /\ j' = j
  /\ j2' = j2
  /\ cs' = cs
  (* Check y *)
  \/ (y = 0 /\ 
      (* Write y and check x *)
      /\ y' = i
      /\ x' = x
      /\ b' = b
      /\ failed' = failed
      /\ j' = j
      /\ j2' = j2
      /\ cs' = cs)
  \/ (y # 0 /\ 
      (* Back off and wait for y to clear *)
      /\ b' = b
      /\ x' = x
      /\ y' = y
      /\ failed' = failed
      /\ j' = j
      /\ j2' = j2
      /\ cs' = cs)

Next == 
  \/ (Proc1)
  \/ \E i \in 2..N : Proc2(i)

Spec == 
  Init /\ [][Next]_<<x, y, b, failed, j, j2, cs>>
  /\ WF_(Proc1)(<<x, y, b, failed, j, j2, cs>>)
  /\ \A i \in 2..N : WF_(Proc2(i))(<<x, y, b, failed, j, j2, cs>>)

Invariant == 
  \A i, j \in 1..N : i # j => ~(cs[i] /\ cs[j])

Liveness == 
  <>[]<>(\E i \in 1..N : cs[i])
=============================================================================