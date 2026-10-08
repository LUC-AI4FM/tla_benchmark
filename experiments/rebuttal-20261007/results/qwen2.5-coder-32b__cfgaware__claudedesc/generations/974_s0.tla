------------------------------- MODULE RegularRegisterAlgorithm -------------------------------

CONSTANTS N

VARIABLES x, y, pc

(* --algorithm RegularRegisterAlgorithm
variables 
  x = [i \in 0..N-1 |-> {0}],
  y = [i \in 0..N-1 |-> 0],
  pc = [i \in 0..N-1 |-> "a1"];

process (P \in 0..N-1)
begin
a1:
  x[P] := {0, 1};
  pc[P] := "a2";
a2:
  x[P] := {1};
  pc[P] := "b";
b:
  y[P] := CHOOSE v \in x[(P - 1) % N];
  pc[P] := "Done";
end process;
*)

Spec ==
  /\ PCInit
  /\ [][Next]_<<x, y, pc>>

PCInit == 
  /\ x = [i \in 0..N-1 |-> {0}]
  /\ y = [i \in 0..N-1 |-> 0]
  /\ pc = [i \in 0..N-1 |-> "a1"]

Next ==
  \/ \E i \in 0..N-1 : pc[i] = "a1" /\ x' = [x EXCEPT ![i] = {0, 1}] /\ y' = y /\ pc' = [pc EXCEPT ![i] = "a2"]
  \/ \E i \in 0..N-1 : pc[i] = "a2" /\ x' = [x EXCEPT ![i] = {1}] /\ y' = y /\ pc' = [pc EXCEPT ![i] = "b"]
  \/ \E i \in 0..N-1 : pc[i] = "b"  /\ x' = x /\ y' = [y EXCEPT ![i] = CHOOSE v \in x[(i - 1) % N]] /\ pc' = [pc EXCEPT ![i] = "Done"]
  \/ \A i \in 0..N-1 : pc[i] = "Done" /\ x' = x /\ y' = y /\ pc' = pc

TypeOK ==
  /\ \A i \in 0..N-1 : x[i] \subseteq {0, 1}
  /\ \A i \in 0..N-1 : y[i] \in {0, 1}
  /\ \A i \in 0..N-1 : pc[i] \in {"a1", "a2", "b", "Done"}

Inv ==
  TypeOK
  /\ \A i \in 0..N-1 : pc[i] \in {"b", "Done"} -> x[i] = {1}
  /\ (\E i \in 0..N-1 : pc[i] \notin {"Done"}) \/ (\E i \in 0..N-1 : y[i] = 1)

PCorrect ==
  []<>(\A i \in 0..N-1 : pc[i] = "Done") => <>[](\E i \in 0..N-1 : y[i] = 1)

THEOREM Correctness == Spec => [](TypeOK /\ Inv)
THEOREM Correctness2 == Spec => []PCorrect

=============================================================================