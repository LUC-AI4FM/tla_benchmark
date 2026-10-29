---------------------------- MODULE RingRegisters ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 1

VARIABLES x, y, pc

vars == <<x, y, pc>>

ProcSet == 0..(N-1)

Left(i) == IF i = 0 THEN N - 1 ELSE i - 1

Init == /\ x  = [i \in ProcSet |-> 0]
        /\ y  = [i \in ProcSet |-> 0]
        /\ pc = [i \in ProcSet |-> "a"]

a(i) == /\ pc[i] = "a"
        /\ x' = [x EXCEPT ![i] = 1]
        /\ pc' = [pc EXCEPT ![i] = "b"]
        /\ UNCHANGED y

b(i) == /\ pc[i] = "b"
        /\ y' = [y EXCEPT ![i] = x[Left(i)]]
        /\ pc' = [pc EXCEPT ![i] = "Done"]
        /\ UNCHANGED x

proc(i) == a(i) \/ b(i)

Terminating == /\ \A i \in ProcSet : pc[i] = "Done"
               /\ UNCHANGED vars

Next == (\E i \in ProcSet : proc(i)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A i \in ProcSet : WF_vars(proc(i))

Termination == <>(\A i \in ProcSet : pc[i] = "Done")

TypeOK == /\ x  \in [ProcSet -> {0, 1}]
          /\ y  \in [ProcSet -> {0, 1}]
          /\ pc \in [ProcSet -> {"a", "b", "Done"}]

PCorrect == (\A i \in ProcSet : pc[i] = "Done") => (\E i \in ProcSet : y[i] = 1)

Inv == /\ TypeOK
       /\ \A i \in ProcSet : pc[i] # "a" => x[i] = 1
       /\ (\E i \in ProcSet : pc[i] # "Done") \/ (\E i \in ProcSet : y[i] = 1)

THEOREM Spec => []PCorrect
=============================================================================