---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, M

ASSUME N \in Nat /\ N >= 1
ASSUME M \in Nat /\ M >= 1 /\ M < N

Procs == 1..N
Group1 == 1..M
Group2 == (M+1)..N

(*--algorithm FastMutex
variables
    x = 0,
    y = 0,
    flag = [i \in Procs |-> FALSE];

define
    MutualExclusion == \A i, j \in Procs : (pc[i] = "cs" /\ pc[j] = "cs") => (i = j)
    Invariant == MutualExclusion
    Liveness == <>(\E i \in Procs : pc[i] = "cs")
end define;

fair process proc1 \in Group1
begin
start1:
    while TRUE do
        flag[self] := TRUE;
    setx1:
        x := self;
    checkx1:
        if y /= 0 then
            flag[self] := FALSE;
        waitx1:
            await y = 0;
            goto start1;
        end if;
    sety1:
        y := self;
    checky1:
        if x /= self then
            flag[self] := FALSE;
        waitflags1:
            await \A j \in Procs : ~flag[j];
        checky2_1:
            if y /= self then
            waity1:
                await y = 0;
                goto start1;
            end if;
        end if;
    cs:
        skip;
    exit1:
        y := 0;
        flag[self] := FALSE;
    end while;
end process;

fair process proc2 \in Group2
begin
start2:
    while TRUE do
        flag[self] := TRUE;
    setx2:
        x := self;
    checkx2:
        if y /= 0 then
            flag[self] := FALSE;
        waitx2:
            await y = 0;
            goto start2;
        end if;
    sety2:
        y := self;
    checky2:
        if x /= self then
            flag[self] := FALSE;
        waitflags2:
            await \A j \in Procs : ~flag[j];
        checky2_2:
            if y /= self then
            waity2:
                await y = 0;
                goto start2;
            end if;
        end if;
    cs2:
        skip;
    exit2:
        y := 0;
        flag[self] := FALSE;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "48a2ac53" /\ chksum(tla) = "5fec81c9")
VARIABLES x, y, flag, pc

(* define statement *)
MutualExclusion == \A i, j \in Procs : (pc[i] = "cs" /\ pc[j] = "cs") => (i = j)
Invariant == MutualExclusion
Liveness == <>(\E i \in Procs : pc[i] = "cs" \/ pc[i] = "cs2")


vars == << x, y, flag, pc >>

ProcSet == (Group1) \cup (Group2)

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ flag = [i \in Procs |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in Group1 -> "start1"
                                        [] self \in Group2 -> "start2"]

start1(self) == /\ pc[self] = "start1"
                /\ flag' = [flag EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "setx1"]
                /\ UNCHANGED << x, y >>

setx1(self) == /\ pc[self] = "setx1"
               /\ x' = self
               /\ pc' = [pc EXCEPT ![self] = "checkx1"]
               /\ UNCHANGED << y, flag >>

checkx1(self) == /\ pc[self] = "checkx1"
                 /\ IF y /= 0
                       THEN /\ flag' = [flag EXCEPT ![self] = FALSE]
                            /\ pc' = [pc EXCEPT ![self] = "waitx1"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "sety1"]
                            /\ flag' = flag
                 /\ UNCHANGED << x, y >>

waitx1(self) == /\ pc[self] = "waitx1"
                /\ y = 0
                /\ pc' = [pc EXCEPT ![self] = "start1"]
                /\ UNCHANGED << x, y, flag >>

sety1(self) == /\ pc[self] = "sety1"
               /\ y' = self
               /\ pc' = [pc EXCEPT ![self] = "checky1"]
               /\ UNCHANGED << x, flag >>

checky1(self) == /\ pc[self] = "checky1"
                 /\ IF x /= self
                       THEN /\ flag' = [flag EXCEPT ![self] = FALSE]
                            /\ pc' = [pc EXCEPT ![self] = "waitflags1"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                            /\ flag' = flag
                 /\ UNCHANGED << x, y >>

waitflags1(self) == /\ pc[self] = "waitflags1"
                    /\ \A j \in Procs : ~flag[j]
                    /\ pc' = [pc EXCEPT ![self] = "checky2_1"]
                    /\ UNCHANGED << x, y, flag >>

checky2_1(self) == /\ pc[self] = "checky2_1"
                   /\ IF y /= self
                         THEN /\ pc' = [pc EXCEPT ![self] = "waity1"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                   /\ UNCHANGED << x, y, flag >>

waity1(self) == /\ pc[self] = "waity1"
                /\ y = 0
                /\ pc' = [pc EXCEPT ![self] = "start1"]
                /\ UNCHANGED << x, y, flag >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit1"]
            /\ UNCHANGED << x, y, flag >>

exit1(self) == /\ pc[self] = "exit1"
               /\ y' = 0
               /\ flag' = [flag EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "start1"]
               /\ UNCHANGED x

proc1(self) == start1(self) \/ setx1(self) \/ checkx1(self)
                  \/ waitx1(self) \/ sety1(self) \/ checky1(self)
                  \/ waitflags1(self) \/ checky2_1(self) \/ waity1(self)
                  \/ cs(self) \/ exit1(self)

start2(self) == /\ pc[self] = "start2"
                /\ flag' = [flag EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "setx2"]
                /\ UNCHANGED << x, y >>

setx2(self) == /\ pc[self] = "setx2"
               /\ x' = self
               /\ pc' = [pc EXCEPT ![self] = "checkx2"]
               /\ UNCHANGED << y, flag >>

checkx2(self) == /\ pc[self] = "checkx2"
                 /\ IF y /= 0
                       THEN /\ flag' = [flag EXCEPT ![self] = FALSE]
                            /\ pc' = [pc EXCEPT ![self] = "waitx2"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "sety2"]
                            /\ flag' = flag
                 /\ UNCHANGED << x, y >>

waitx2(self) == /\ pc[self] = "waitx2"
                /\ y = 0
                /\ pc' = [pc EXCEPT ![self] = "start2"]
                /\ UNCHANGED << x, y, flag >>

sety2(self) == /\ pc[self] = "sety2"
               /\ y' = self
               /\ pc' = [pc EXCEPT ![self] = "checky2"]
               /\ UNCHANGED << x, flag >>

checky2(self) == /\ pc[self] = "checky2"
                 /\ IF x /= self
                       THEN /\ flag' = [flag EXCEPT ![self] = FALSE]
                            /\ pc' = [pc EXCEPT ![self] = "waitflags2"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "cs2"]
                            /\ flag' = flag
                 /\ UNCHANGED << x, y >>

waitflags2(self) == /\ pc[self] = "waitflags2"
                    /\ \A j \in Procs : ~flag[j]
                    /\ pc' = [pc EXCEPT ![self] = "checky2_2"]
                    /\ UNCHANGED << x, y, flag >>

checky2_2(self) == /\ pc[self] = "checky2_2"
                   /\ IF y /= self
                         THEN /\ pc' = [pc EXCEPT ![self] = "waity2"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "cs2"]
                   /\ UNCHANGED << x, y, flag >>

waity2(self) == /\ pc[self] = "waity2"
                /\ y = 0
                /\ pc' = [pc EXCEPT ![self] = "start2"]
                /\ UNCHANGED << x, y, flag >>

cs2(self) == /\ pc[self] = "cs2"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "exit2"]
             /\ UNCHANGED << x, y, flag >>

exit2(self) == /\ pc[self] = "exit2"
               /\ y' = 0
               /\ flag' = [flag EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "start2"]
               /\ UNCHANGED x

proc2(self) == start2(self) \/ setx2(self) \/ checkx2(self)
                  \/ waitx2(self) \/ sety2(self) \/ checky2(self)
                  \/ waitflags2(self) \/ checky2_2(self) \/ waity2(self)
                  \/ cs2(self) \/ exit2(self)

Next == (\E self \in Group1: proc1(self))
           \/ (\E self \in Group2: proc2(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Group1 : WF_vars(proc1(self))
        /\ \A self \in Group2 : WF_vars(proc2(self))

\* END TRANSLATION

==========================================================================