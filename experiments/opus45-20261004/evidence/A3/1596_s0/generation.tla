---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, TLAPS

CONSTANTS M, N

ASSUME ConstantAssumptions == /\ M \in Nat
                              /\ N \in Nat
                              /\ M > 0
                              /\ N >= M

Procs1 == 1..M
Procs2 == (M+1)..N
Procs == Procs1 \cup Procs2

(*--algorithm FastMutex
variables
    x = 0;
    y = 0;
    b = [i \in Procs |-> FALSE];

define
    MutualExclusion == \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")
end define;

fair process Proc1 \in Procs1
begin
start1:
    b[self] := TRUE;
setx1:
    x := self;
checkx1:
    if y # 0 then
        goto resetb1;
    end if;
sety1:
    y := self;
checky1:
    if x # self then
        goto slowpath1;
    end if;
    goto cs;
slowpath1:
    b[self] := FALSE;
waitb1:
    await \A j \in Procs : ~b[j] \/ j = self;
checky2_1:
    if y # self then
        goto waity1;
    end if;
    goto cs;
waity1:
    await y = 0;
    goto start1;
resetb1:
    b[self] := FALSE;
waity2_1:
    await y = 0;
    goto start1;
cs:
    skip;
exit1:
    y := 0;
    b[self] := FALSE;
    goto start1;
end process;

fair process Proc2 \in Procs2
begin
start2:
    b[self] := TRUE;
setx2:
    x := self;
checkx2:
    if y # 0 then
        goto resetb2;
    end if;
sety2:
    y := self;
checky2:
    if x # self then
        goto slowpath2;
    end if;
    goto cs2;
slowpath2:
    b[self] := FALSE;
waitb2:
    await \A j \in Procs : ~b[j] \/ j = self;
checky2_2:
    if y # self then
        goto waity2;
    end if;
    goto cs2;
waity2:
    await y = 0;
    goto start2;
resetb2:
    b[self] := FALSE;
waity2_2:
    await y = 0;
    goto start2;
cs2:
    skip;
exit2:
    y := 0;
    b[self] := FALSE;
    goto start2;
end process;

end algorithm; *)

VARIABLES x, y, b, pc

vars == << x, y, b, pc >>

ProcSet == (Procs1) \cup (Procs2)

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in Procs |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in Procs1 -> "start1"
                                        [] self \in Procs2 -> "start2"]

start1(self) == /\ pc[self] = "start1"
                /\ b' = [b EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "setx1"]
                /\ UNCHANGED << x, y >>

setx1(self) == /\ pc[self] = "setx1"
               /\ x' = self
               /\ pc' = [pc EXCEPT ![self] = "checkx1"]
               /\ UNCHANGED << y, b >>

checkx1(self) == /\ pc[self] = "checkx1"
                 /\ IF y # 0
                       THEN /\ pc' = [pc EXCEPT ![self] = "resetb1"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "sety1"]
                 /\ UNCHANGED << x, y, b >>

sety1(self) == /\ pc[self] = "sety1"
               /\ y' = self
               /\ pc' = [pc EXCEPT ![self] = "checky1"]
               /\ UNCHANGED << x, b >>

checky1(self) == /\ pc[self] = "checky1"
                 /\ IF x # self
                       THEN /\ pc' = [pc EXCEPT ![self] = "slowpath1"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                 /\ UNCHANGED << x, y, b >>

slowpath1(self) == /\ pc[self] = "slowpath1"
                   /\ b' = [b EXCEPT ![self] = FALSE]
                   /\ pc' = [pc EXCEPT ![self] = "waitb1"]
                   /\ UNCHANGED << x, y >>

waitb1(self) == /\ pc[self] = "waitb1"
                /\ \A j \in Procs : ~b[j] \/ j = self
                /\ pc' = [pc EXCEPT ![self] = "checky2_1"]
                /\ UNCHANGED << x, y, b >>

checky2_1(self) == /\ pc[self] = "checky2_1"
                   /\ IF y # self
                         THEN /\ pc' = [pc EXCEPT ![self] = "waity1"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                   /\ UNCHANGED << x, y, b >>

waity1(self) == /\ pc[self] = "waity1"
                /\ y = 0
                /\ pc' = [pc EXCEPT ![self] = "start1"]
                /\ UNCHANGED << x, y, b >>

resetb1(self) == /\ pc[self] = "resetb1"
                 /\ b' = [b EXCEPT ![self] = FALSE]
                 /\ pc' = [pc EXCEPT ![self] = "waity2_1"]
                 /\ UNCHANGED << x, y >>

waity2_1(self) == /\ pc[self] = "waity2_1"
                  /\ y = 0
                  /\ pc' = [pc EXCEPT ![self] = "start1"]
                  /\ UNCHANGED << x, y, b >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit1"]
            /\ UNCHANGED << x, y, b >>

exit1(self) == /\ pc[self] = "exit1"
               /\ y' = 0
               /\ b' = [b EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "start1"]
               /\ UNCHANGED x

Proc1(self) == start1(self) \/ setx1(self) \/ checkx1(self) \/ sety1(self)
                  \/ checky1(self) \/ slowpath1(self) \/ waitb1(self)
                  \/ checky2_1(self) \/ waity1(self) \/ resetb1(self)
                  \/ waity2_1(self) \/ cs(self) \/ exit1(self)

start2(self) == /\ pc[self] = "start2"
                /\ b' = [b EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "setx2"]
                /\ UNCHANGED << x, y >>

setx2(self) == /\ pc[self] = "setx2"
               /\ x' = self
               /\ pc' = [pc EXCEPT ![self] = "checkx2"]
               /\ UNCHANGED << y, b >>

checkx2(self) == /\ pc[self] = "checkx2"
                 /\ IF y # 0
                       THEN /\ pc' = [pc EXCEPT ![self] = "resetb2"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "sety2"]
                 /\ UNCHANGED << x, y, b >>

sety2(self) == /\ pc[self] = "sety2"
               /\ y' = self
               /\ pc' = [pc EXCEPT ![self] = "checky2"]
               /\ UNCHANGED << x, b >>

checky2(self) == /\ pc[self] = "checky2"
                 /\ IF x # self
                       THEN /\ pc' = [pc EXCEPT ![self] = "slowpath2"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "cs2"]
                 /\ UNCHANGED << x, y, b >>

slowpath2(self) == /\ pc[self] = "slowpath2"
                   /\ b' = [b EXCEPT ![self] = FALSE]
                   /\ pc' = [pc EXCEPT ![self] = "waitb2"]
                   /\ UNCHANGED << x, y >>

waitb2(self) == /\ pc[self] = "waitb2"
                /\ \A j \in Procs : ~b[j] \/ j = self
                /\ pc' = [pc EXCEPT ![self] = "checky2_2"]
                /\ UNCHANGED << x, y, b >>

checky2_2(self) == /\ pc[self] = "checky2_2"
                   /\ IF y # self
                         THEN /\ pc' = [pc EXCEPT ![self] = "waity2"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "cs2"]
                   /\ UNCHANGED << x, y, b >>

waity2(self) == /\ pc[self] = "waity2"
                /\ y = 0
                /\ pc' = [pc EXCEPT ![self] = "start2"]
                /\ UNCHANGED << x, y, b >>

resetb2(self) == /\ pc[self] = "resetb2"
                 /\ b' = [b EXCEPT ![self] = FALSE]
                 /\ pc' = [pc EXCEPT ![self] = "waity2_2"]
                 /\ UNCHANGED << x, y >>

waity2_2(self) == /\ pc[self] = "waity2_2"
                  /\ y = 0
                  /\ pc' = [pc EXCEPT ![self] = "start2"]
                  /\ UNCHANGED << x, y, b >>

cs2(self) == /\ pc[self] = "cs2"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "exit2"]
             /\ UNCHANGED << x, y, b >>

exit2(self) == /\ pc[self] = "exit2"
               /\ y' = 0
               /\ b' = [b EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "start2"]
               /\ UNCHANGED x

Proc2(self) == start2(self) \/ setx2(self) \/ checkx2(self) \/ sety2(self)
                  \/ checky2(self) \/ slowpath2(self) \/ waitb2(self)
                  \/ checky2_2(self) \/ waity2(self) \/ resetb2(self)
                  \/ waity2_2(self) \/ cs2(self) \/ exit2(self)

Next == (\E self \in Procs1: Proc1(self))
           \/ (\E self \in Procs2: Proc2(self))

Spec == Init /\ [][Next]_vars
           /\ \A self \in Procs1 : WF_vars(Proc1(self))
           /\ \A self \in Procs2 : WF_vars(Proc2(self))

\* Safety invariant: Mutual Exclusion
MutualExclusion == \A i, j \in Procs : (i # j) => ~((pc[i] = "cs" \/ pc[i] = "cs2") /\ (pc[j] = "cs" \/ pc[j] = "cs2"))

\* Liveness property: Some process enters the critical section infinitely often
InCS == \E i \in Procs : pc[i] = "cs" \/ pc[i] = "cs2"
Liveness == []<>InCS

==========================================================================