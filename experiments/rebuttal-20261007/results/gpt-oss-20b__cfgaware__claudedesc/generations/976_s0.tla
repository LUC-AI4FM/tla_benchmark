------------------------------ MODULE SimpleConcurrent ------------------------------
EXTENDS Naturals, Integers, Sequences

CONSTANT N

VARIABLES x, y, pc

(* Helper: index of the left neighbor *)
left(i) == (i - 1 + N) % N

(* Type correctness invariant *)
TypeOK ==
  /\ x \in [0..N-1 -> {0,1}]
  /\ y \in [0..N-1 -> {0,1}]
  /\ pc \in [0..N-1 -> {"a","b","Done"}]

(* Initial state *)
Init ==
  /\ TypeOK
  /\ x = [i \in 0..N-1 |-> 0]
  /\ y = [i \in 0..N-1 |-> 0]
  /\ pc = [i \in 0..N-1 |-> "a"]

(* Next-state relation *)
Next ==
  \E i \in 0..N-1 :
    /\ pc[i] = "a"
    /\ x' = [x EXCEPT ![i] = 1]
    /\ pc' = [pc EXCEPT ![i] = "b"]
    /\ y' = y
  \/ \E j \in 0..N-1 :
      LET val == x[left(j)] IN
          ( /\ pc[j] = "b"
            /\ y' = [y EXCEPT ![j] = val]
            /\ pc' = [pc EXCEPT ![j] = "Done"]
            /\ x' = x )

Spec ==
  Init /\ [][Next]_<<x, y, pc>>

(* Invariant combining type correctness and progress *)
Inv ==
  TypeOK
  /\ (\A i \in 0..N-1 : pc[i] # "a" => x[i] = 1)
  /\ ((\E i \in 0..N-1 : pc[i] # "Done") \/ (\E j \in 0..N-1 : y[j] = 1))

(* Correctness property: when all processes are Done, some y is 1 *)
PCorrect ==
  (\A i \in 0..N-1 : pc[i] = "Done")
  => (\E j \in 0..N-1 : y[j] = 1)

=============================================================================