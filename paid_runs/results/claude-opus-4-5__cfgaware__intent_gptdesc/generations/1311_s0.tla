---------------------------- MODULE GCD ----------------------------

EXTENDS Integers, Naturals, FiniteSets

CONSTANTS M, N_max

ASSUME M \in Nat /\ M > 0
ASSUME N_max \in Nat /\ N_max > 0

VARIABLES x, y, pc

vars == <<x, y, pc>>

TypeOK == 
    /\ x \in Nat
    /\ y \in Nat
    /\ pc \in {"running", "done"}

GCD(a, b) == 
    LET RECURSIVE GCDHelper(_, _)
        GCDHelper(m, n) == 
            IF n = 0 THEN m
            ELSE GCDHelper(n, m % n)
    IN IF a >= b THEN GCDHelper(a, b) ELSE GCDHelper(b, a)

Init == 
    /\ x = M
    /\ y \in 1..N_max
    /\ pc = "running"

Step == 
    /\ pc = "running"
    /\ x > 0
    /\ y > 0
    /\ IF x >= y 
       THEN x' = x - y /\ y' = y
       ELSE y' = y - x /\ x' = x
    /\ pc' = "running"

Terminate == 
    /\ pc = "running"
    /\ (x = 0 \/ y = 0)
    /\ pc' = "done"
    /\ UNCHANGED <<x, y>>

Next == Step \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "done")

NonNegative == x >= 0 /\ y >= 0

Bounded == x <= M + N_max /\ y <= M + N_max

Safety == NonNegative /\ Bounded

GCDPreserved == 
    pc = "running" => 
        (x = 0 \/ y = 0 \/ GCD(x, y) = GCD(M, y))

TerminationCorrect == 
    pc = "done" => 
        ((x = 0 /\ y > 0) \/ (y = 0 /\ x > 0))

Invariant == TypeOK /\ NonNegative /\ Bounded

=================================================================