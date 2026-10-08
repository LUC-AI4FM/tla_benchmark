EXTENDS Naturals

CONSTANT N

VARIABLES A, B, pc

Proc == 0 .. N-1

TypeOK ==
    /\ A \in [Proc -> 0..1]
    /\ B \in [Proc -> 0..1]
    /\ pc \in [Proc -> {0,1,2}]

Init ==
    /\ A = [i \in Proc |-> 0]
    /\ B = [i \in Proc |-> 0]
    /\ pc = [i \in Proc |-> 0]

WriteStep(i) ==
    /\ i \in Proc
    /\ pc[i] = 0
    /\ A' = [A EXCEPT ![i] = 1]
    /\ pc' = [pc EXCEPT ![i] = 1]
    /\ B' = B

ReadStep(i) ==
    /\ i \in Proc
    /\ pc[i] = 1
    /\ left == (i - 1 + N) % N
    /\ B' = [B EXCEPT ![i] = A[left]]
    /\ pc' = [pc EXCEPT ![i] = 2]
    /\ A' = A

Next ==
    \E i \in Proc : WriteStep(i) \/ ReadStep(i)

Spec == Init /\ [][Next]_<<A,B,pc>> /\ WF_<<A,B,pc>>(Next)

AllTerminated == \A i \in Proc : pc[i] = 2

PCorrect == AllTerminated => (\E j \in Proc : B[j] = 1)

Inv ==
    TypeOK /\
    (\A i \in Proc :
        (pc[i] = 0 /\ A[i] = 0 /\ B[i] = 0) \/ 
        (pc[i] = 1 /\ A[i] = 1 /\ B[i] = 0) \/ 
        (pc[i] = 2 /\ A[i] = 1 /\ B[i] = A[(i - 1 + N) % N]))