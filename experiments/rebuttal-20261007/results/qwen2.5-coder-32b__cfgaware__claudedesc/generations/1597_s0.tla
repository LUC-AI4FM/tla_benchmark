------------------------------- MODULE FastMutex -------------------------------

CONSTANTS N \* Number of processes

VARIABLES x, y, b, pc

\* Process identifiers
Proc1 == 1
Proc2 == {2 .. N}

Procs == {Proc1} \cup Proc2

\* Initial state
Init == /\ x = 0
        /\ y = 0
        /\ b = [p \in Procs |-> FALSE]
        /\ pc = [p \in Procs |-> "entry"]

\* Macros for process actions
MacroSetB(p) ==
    /\ b' = [b EXCEPT ![p] = TRUE]

MacroClearB(p) ==
    /\ b' = [b EXCEPT ![p] = FALSE]

MacroWriteX(p) ==
    /\ x' = p

MacroWriteY(p) ==
    /\ y' = p

MacroResetY() ==
    /\ y' = 0

\* Process actions
Entry(p) ==
    \* Set b[p]
    /\ MacroSetB(p)
    /\ pc' = [pc EXCEPT ![p] = "writeX"]

WriteX(p) ==
    \* Write x := p
    /\ MacroWriteX(p)
    /\ pc' = [pc EXCEPT ![p] = "checkY"]

CheckY(p) ==
    \* Check y == 0
    /\ IF y = 0 THEN pc' = [pc EXCEPT ![p] = "writeY"]
     ELSE pc' = [pc EXCEPT ![p] = "backoff"]

WriteY(p) ==
    \* Write y := p
    /\ MacroWriteY(p)
    /\ pc' = [pc EXCEPT ![p] = "checkX"]

CheckX(p) ==
    \* Check x == p
    /\ IF x = p THEN pc' = [pc EXCEPT ![p] = "critical"]
     ELSE pc' = [pc EXCEPT ![p] = "clearBWait"]

Backoff(p) ==
    \* Wait for y to be 0
    /\ IF y = 0 THEN pc' = [pc EXCEPT ![p] = "writeY"]
     ELSE pc' = [pc EXCEPT ![p] = "backoff"]

ClearBWait(p) ==
    \* Clear b[p] and wait for all other b[q] to be false
    /\ MacroClearB(p)
    /\ IF (\A q \in Procs \ {p} : ~b[q]) THEN pc' = [pc EXCEPT ![p] = "checkYAgain"]
     ELSE pc' = [pc EXCEPT ![p] = "clearBWait"]

CheckYAgain(p) ==
    \* Check y == p
    /\ IF y = p THEN pc' = [pc EXCEPT ![p] = "critical"]
     ELSE /\ pc' = [pc EXCEPT ![p] = "failed"]
          /\ x' = 0

Failed(p) ==
    \* Set failed flag and reset b[p]
    /\ MacroClearB(p)
    /\ pc' = [pc EXCEPT ![p] = "entry"]

Critical(p) ==
    \* Critical section
    /\ pc' = [pc EXCEPT ![p] = "exit"]

Exit(p) ==
    \* Reset y := 0 and clear b[p]
    /\ MacroResetY()
    /\ MacroClearB(p)
    /\ pc' = [pc EXCEPT ![p] = "entry"]

\* Next-state relation
Next == 
    \/ p \in Procs : /\ pc[p] = "entry"     /\ Entry(p)
                  \/ pc[p] = "writeX"    /\ WriteX(p)
                  \/ pc[p] = "checkY"    /\ CheckY(p)
                  \/ pc[p] = "writeY"    /\ WriteY(p)
                  \/ pc[p] = "checkX"    /\ CheckX(p)
                  \/ pc[p] = "backoff"   /\ Backoff(p)
                  \/ pc[p] = "clearBWait" /\ ClearBWait(p)
                  \/ pc[p] = "checkYAgain" /\ CheckYAgain(p)
                  \/ pc[p] = "failed"    /\ Failed(p)
                  \/ pc[p] = "critical"  /\ Critical(p)
                  \/ pc[p] = "exit"      /\ Exit(p)

\* Specification
Spec == Init /\ [][Next]_<<pc>>

\* Mutual exclusion invariant
Invariant ==
    \A p, q \in Procs : p # q => ~(\E s \in StateSpace: s.pc[p] = "critical" /\ s.pc[q] = "critical")

\* Liveness property
Liveness ==
    \A p \in Procs : <>[](pc[p] = "critical")

=============================================================================