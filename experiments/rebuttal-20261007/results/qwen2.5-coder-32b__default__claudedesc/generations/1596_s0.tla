------------------------------- MODULE FastMutex2 -------------------------------
EXTENDS Naturals, TLC

CONSTANTS N, M

VARIABLES x, y, b, loop1, loop2, fail1, fail2

Proc1 == 1..M
Proc2 == (M+1)..N

Init == /\ x = 0 
        /\ y = 0 
        /\ b = [p \in 1..N -> FALSE] 
        /\ loop1 = 0 
        /\ loop2 = 0 
        /\ fail1 = FALSE 
        /\ fail2 = FALSE

Next == \/ \E p \in Proc1 : FastMutex(p)
        \/ \E p \in Proc2 : FastMutex(p)

FastMutex(p) ==
    LET flag == IF p \in Proc1 THEN fail1 ELSE fail2
        loop == IF p \in Proc1 THEN loop1 ELSE loop2
        new_loop == loop + 1
        new_fail == FALSE
    IN /\ b' = [b EXCEPT ![p] = TRUE]
       /\ x' = p
       /\ y # 0 -> \/ b' = [b EXCEPT ![p] = FALSE]
                      /\ UNCHANGED <<x, y, loop1, loop2, fail1, fail2>>
       /\ y = 0 -> \/ y' = p
                      /\ IF x # p THEN \/ b' = [b EXCEPT ![p] = FALSE]
                                             /\ new_fail
                                             /\ UNCHANGED <<x, loop1, loop2>>
                                          ELSE \/ UNCHANGED <<x, y', b, loop1, loop2>>
       /\ flag -> \/ y' = 0
                     /\ b' = [b EXCEPT ![p] = FALSE]
                     /\ IF p \in Proc1 THEN fail1' = new_fail
                                           ELSE fail2' = new_fail
                     /\ IF p \in Proc1 THEN loop1' = new_loop
                                           ELSE loop2' = new_loop
       /\ ~flag -> \/ UNCHANGED <<x, y', b>>
                      /\ IF p \in Proc1 THEN loop1' = new_loop
                                            ELSE loop2' = new_loop

Spec == Init /\ [][Next]_<<x, y, b, loop1, loop2, fail1, fail2>> /\ WF_next(Next)

MutualExclusion == \/ y = 0 
                     \/ \A p1, p2 \in 1..N : p1 # p2 => (y # p1) \/ (y # p2) \/ (fail1 \/ fail2)

Liveness == <>[] (\E p \in 1..N : y = p /\ ~(p \in Proc1 => fail1 \/ p \in Proc2 => fail2))

=============================================================================