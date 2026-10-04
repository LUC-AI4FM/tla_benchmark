---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 2

(*--algorithm FastMutex
variables x = 0, y = 0, b = [i \in 1..N |-> FALSE];

fair process Proc1 = 1
variables failed1 = FALSE;
begin
start1:
    while TRUE do
        b[1] := TRUE;
    
    setx1:
        x := 1;
    
    checky1:
        if y /= 0 then
            b[1] := FALSE;
        wait1:
            await y = 0;
            goto start1;
        end if;
    
    sety1:
        y := 1;
    
    checkx1:
        if x /= 1 then
            b[1] := FALSE;
        waitb1:
            await \A j \in 2..N : ~b[j];
        checky2_1:
            if y /= 1 then
                await y = 0;
                goto start1;
            end if;
        end if;
    
    cs1:
        skip;
    
    exit1:
        y := 0;
        b[1] := FALSE;
    end while;
end process;

fair process ProcN \in 2..N
variables failedN = FALSE;
begin
startN:
    while TRUE do
        b[self] := TRUE;
    
    setxN:
        x := self;
    
    checkyN:
        if y /= 0 then
            b[self] := FALSE;
        waitN:
            await y = 0;
            goto startN;
        end if;
    
    setyN:
        y := self;
    
    checkxN:
        if x /= self then
            b[self] := FALSE;
        waitbN:
            await \A j \in 1..N : j = self \/ ~b[j];
        checky2N:
            if y /= self then
                await y = 0;
                goto startN;
            end if;
        end if;
    
    csN:
        skip;
    
    exitN:
        y := 0;
        b[self] := FALSE;
    end while;
end process;

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES x, y, b, pc, failed1, failedN

vars == << x, y, b, pc, failed1, failedN >>

ProcSet == {1} \cup (2..N)

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        (* Process Proc1 *)
        /\ failed1 = FALSE
        (* Process ProcN *)
        /\ failedN = [self \in 2..N |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "start1"
                                        [] self \in 2..N -> "startN"]

start1 == /\ pc[1] = "start1"
          /\ b' = [b EXCEPT ![1] = TRUE]
          /\ pc' = [pc EXCEPT ![1] = "setx1"]
          /\ UNCHANGED << x, y, failed1, failedN >>

setx1 == /\ pc[1] = "setx1"
         /\ x' = 1
         /\ pc' = [pc EXCEPT ![1] = "checky1"]
         /\ UNCHANGED << y, b, failed1, failedN >>

checky1 == /\ pc[1] = "checky1"
           /\ IF y /= 0
                 THEN /\ b' = [b EXCEPT ![1] = FALSE]
                      /\ pc' = [pc EXCEPT ![1] = "wait1"]
                 ELSE /\ pc' = [pc EXCEPT ![1] = "sety1"]
                      /\ b' = b
           /\ UNCHANGED << x, y, failed1, failedN >>

wait1 == /\ pc[1] = "wait1"
         /\ y = 0
         /\ pc' = [pc EXCEPT ![1] = "start1"]
         /\ UNCHANGED << x, y, b, failed1, failedN >>

sety1 == /\ pc[1] = "sety1"
         /\ y' = 1
         /\ pc' = [pc EXCEPT ![1] = "checkx1"]
         /\ UNCHANGED << x, b, failed1, failedN >>

checkx1 == /\ pc[1] = "checkx1"
           /\ IF x /= 1
                 THEN /\ b' = [b EXCEPT ![1] = FALSE]
                      /\ pc' = [pc EXCEPT ![1] = "waitb1"]
                 ELSE /\ pc' = [pc EXCEPT ![1] = "cs1"]
                      /\ b' = b
           /\ UNCHANGED << x, y, failed1, failedN >>

waitb1 == /\ pc[1] = "waitb1"
          /\ \A j \in 2..N : ~b[j]
          /\ pc' = [pc EXCEPT ![1] = "checky2_1"]
          /\ UNCHANGED << x, y, b, failed1, failedN >>

checky2_1 == /\ pc[1] = "checky2_1"
             /\ IF y /= 1
                   THEN /\ y = 0
                        /\ pc' = [pc EXCEPT ![1] = "start1"]
                   ELSE /\ pc' = [pc EXCEPT ![1] = "cs1"]
             /\ UNCHANGED << x, y, b, failed1, failedN >>

cs1 == /\ pc[1] = "cs1"
       /\ TRUE
       /\ pc' = [pc EXCEPT ![1] = "exit1"]
       /\ UNCHANGED << x, y, b, failed1, failedN >>

exit1 == /\ pc[1] = "exit1"
         /\ y' = 0
         /\ b' = [b EXCEPT ![1] = FALSE]
         /\ pc' = [pc EXCEPT ![1] = "start1"]
         /\ UNCHANGED << x, failed1, failedN >>

Proc1 == start1 \/ setx1 \/ checky1 \/ wait1 \/ sety1 \/ checkx1 
            \/ waitb1 \/ checky2_1 \/ cs1 \/ exit1

startN(self) == /\ pc[self] = "startN"
                /\ b' = [b EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "setxN"]
                /\ UNCHANGED << x, y, failed1, failedN >>

setxN(self) == /\ pc[self] = "setxN"
               /\ x' = self
               /\ pc' = [pc EXCEPT ![self] = "checkyN"]
               /\ UNCHANGED << y, b, failed1, failedN >>

checkyN(self) == /\ pc[self] = "checkyN"
                 /\ IF y /= 0
                       THEN /\ b' = [b EXCEPT ![self] = FALSE]
                            /\ pc' = [pc EXCEPT ![self] = "waitN"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "setyN"]
                            /\ b' = b
                 /\ UNCHANGED << x, y, failed1, failedN >>

waitN(self) == /\ pc[self] = "waitN"
               /\ y = 0
               /\ pc' = [pc EXCEPT ![self] = "startN"]
               /\ UNCHANGED << x, y, b, failed1, failedN >>

setyN(self) == /\ pc[self] = "setyN"
               /\ y' = self
               /\ pc' = [pc EXCEPT ![self] = "checkxN"]
               /\ UNCHANGED << x, b, failed1, failedN >>

checkxN(self) == /\ pc[self] = "checkxN"
                 /\ IF x /= self
                       THEN /\ b' = [b EXCEPT ![self] = FALSE]
                            /\ pc' = [pc EXCEPT ![self] = "waitbN"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "csN"]
                            /\ b' = b
                 /\ UNCHANGED << x, y, failed1, failedN >>

waitbN(self) == /\ pc[self] = "waitbN"
                /\ \A j \in 1..N : j = self \/ ~b[j]
                /\ pc' = [pc EXCEPT ![self] = "checky2N"]
                /\ UNCHANGED << x, y, b, failed1, failedN >>

checky2N(self) == /\ pc[self] = "checky2N"
                  /\ IF y /= self
                        THEN /\ y = 0
                             /\ pc' = [pc EXCEPT ![self] = "startN"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "csN"]
                  /\ UNCHANGED << x, y, b, failed1, failedN >>

csN(self) == /\ pc[self] = "csN"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "exitN"]
             /\ UNCHANGED << x, y, b, failed1, failedN >>

exitN(self) == /\ pc[self] = "exitN"
               /\ y' = 0
               /\ b' = [b EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "startN"]
               /\ UNCHANGED << x, failed1, failedN >>

ProcN(self) == startN(self) \/ setxN(self) \/ checkyN(self) \/ waitN(self)
                  \/ setyN(self) \/ checkxN(self) \/ waitbN(self) 
                  \/ checky2N(self) \/ csN(self) \/ exitN(self)

Next == Proc1
           \/ (\E self \in 2..N: ProcN(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Proc1)
        /\ \A self \in 2..N : WF_vars(ProcN(self))

\* END TRANSLATION

-----------------------------------------------------------------------------

(* Critical section predicate: process i is in the critical section *)
InCS(i) == IF i = 1 THEN pc[1] = "cs1" ELSE pc[i] = "csN"

(* Mutual exclusion invariant: no two distinct processes are simultaneously in CS *)
MutualExclusion == \A i, j \in 1..N : (i /= j) => ~(InCS(i) /\ InCS(j))

Invariant == MutualExclusion

(* Liveness: infinitely often some process is in the critical section *)
Liveness == []<>(\E i \in 1..N : InCS(i))

=============================================================================