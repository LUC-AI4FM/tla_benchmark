-------------------------- MODULE RegularRegister --------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N
ASSUME N \in Nat /\ N > 0

VARIABLES pc, x, y

vars == <<pc, x, y>>
ProcSet == 1..N

PC_VALS == {"Start", "MidWrite", "PostWrite", "Done"}
VALS == {0, 1}

Neighbor(i) == (i % N) + 1

TypeOK ==
    /\ pc \in [ProcSet -> PC_VALS]
    /\ x \in [ProcSet -> SUBSET VALS]
    /\ y \in [ProcSet -> VALS]
    /\ \A i \in ProcSet :
        \/ (pc[i] = "Start") /\ (x[i] = {0})
        \/ (pc[i] = "MidWrite") /\ (x[i] = {0, 1})
        \/ (pc[i] \in {"PostWrite", "Done"}) /\ (x[i] = {1})

Init ==
    /\ pc = [i \in ProcSet |-> "Start"]
    /\ x  = [i \in ProcSet |-> {0}]
    /\ y  = [i \in ProcSet |-> 0]

StartWrite(i) ==
    /\ pc[i] = "Start"
    /\ pc' = [pc EXCEPT ![i] = "MidWrite"]
    /\ x'  = [x EXCEPT ![i] = {0, 1}]
    /\ UNCHANGED y

FinishWrite(i) ==
    /\ pc[i] = "MidWrite"
    /\ pc' = [pc EXCEPT ![i] = "PostWrite"]
    /\ x'  = [x EXCEPT ![i] = {1}]
    /\ UNCHANGED y

ReadNeighbor(i) ==
    /\ pc[i] = "PostWrite"
    /\ \E v \in x[Neighbor(i)] :
        y' = [y EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "Done"]
    /\ UNCHANGED x

Next == \E i \in ProcSet :
    \/ StartWrite(i)
    \/ FinishWrite(i)
    \/ ReadNeighbor(i)

Spec == Init /\ [][Next]_vars

Termination == \A i \in ProcSet : pc[i] = "Done"

PCorrect == Termination => (\E i \in ProcSet : y[i] = 1)

(* The inductive invariant used to prove PCorrect. *)
Inv == TypeOK /\
       (\A i \in ProcSet :
           (pc[i] = "Done" /\ y[i] = 0) => (pc[Neighbor(i)] \in {"Start", "MidWrite"}))

=============================================================================