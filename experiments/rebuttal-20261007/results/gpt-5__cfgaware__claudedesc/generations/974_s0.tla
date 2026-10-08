----------------------------- MODULE RegularVariant -----------------------------

EXTENDS Naturals

CONSTANT N

\* Process identifiers
Proc == 0..(N-1)

\* State variables
VARIABLES x, y, pc

vars == << x, y, pc >>

\* Predecessor in the ring, i.e., (i-1) mod N
Prev(i) == IF i = 0 THEN N - 1 ELSE i - 1

\* Initial state: all processes at a1, all x[i] hold stable 0, all y[i] = 0
Init ==
  /\ x = [i \in Proc |-> {0}]
  /\ y = [i \in Proc |-> 0]
  /\ pc = [i \in Proc |-> "a1"]

\* Step a1: start writing 1 by placing the regular register in transient state {0,1}
A1(i) ==
  /\ i \in Proc
  /\ pc[i] = "a1"
  /\ x'  = [x EXCEPT ![i] = {0,1}]
  /\ pc' = [pc EXCEPT ![i] = "a2"]
  /\ UNCHANGED y

\* Step a2: complete the write by setting the register to {1}
A2(i) ==
  /\ i \in Proc
  /\ pc[i] = "a2"
  /\ x'  = [x EXCEPT ![i] = {1}]
  /\ pc' = [pc EXCEPT ![i] = "b"]
  /\ UNCHANGED y

\* Step b: read any value currently in predecessor's regular register
B(i) ==
  /\ i \in Proc
  /\ pc[i] = "b"
  /\ \E v \in x[Prev(i)]:
        /\ y'  = [y EXCEPT ![i] = v]
        /\ pc' = [pc EXCEPT ![i] = "Done"]
        /\ UNCHANGED x

Next ==
  \E i \in Proc: A1(i) \/ A2(i) \/ B(i)

\* Liveness: every process eventually reaches Done
Termination ==
  \A i \in Proc: <> (pc[i] = "Done")

Spec == Init /\ [][Next]_vars /\ Termination

\* Type correctness for variables, including non-empty regular-register values
TypeOK ==
  /\ x \in [Proc -> SUBSET {0,1}]
  /\ \A i \in Proc: x[i] # {}
  /\ y \in [Proc -> {0,1}]
  /\ pc \in [Proc -> {"a1","a2","b","Done"}]

\* Inductive invariant:
\*  - if a process is at or past b, then its write is complete: x[i] = {1}
\*  - either someone is not done yet, or some y[i] equals 1
Inv ==
  /\ TypeOK
  /\ \A i \in Proc: (pc[i] \in {"b","Done"}) => x[i] = {1}
  /\ (\E i \in Proc: pc[i] # "Done") \/ (\E i \in Proc: y[i] = 1)

\* Safety property: when all processes are Done, at least one read value is 1
PCorrect ==
  (\A i \in Proc: pc[i] = "Done") => (\E i \in Proc: y[i] = 1)

==================================