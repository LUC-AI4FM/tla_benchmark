---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

(*
--algorithm FastMutex
variables x = 0, y = 0, b = [i \in Procs |-> FALSE];

process proc \in Procs
variable S = {};
begin
start:
    b[self] := TRUE;
l1:
    x := self;
l2:
    if y /= 0 then
        b[self] := FALSE;
l3:
        await y = 0;
        goto start;
    end if;
l4:
    y := self;
l5:
    if x /= self then
        b[self] := FALSE;
l6:
        S := Procs \ {self};
l7:
        while S /= {} do
            with p \in S do
                await ~b[p];
                S := S \ {p};
            end with;
        end while;
l8:
        if y /= self then
l9:
            await y = 0;
            goto start;
        end if;
    end if;
cs:
    skip;
l10:
    y := 0;
    b[self] := FALSE;
    goto start;
end process;
end algorithm
*)

VARIABLES x, y, b, pc, S

vars == << x, y, b, pc, S >>

ProcSet == (Procs)

Init == 
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ S = [self \in Procs |-> {}]
    /\ pc = [self \in ProcSet |-> "start"]

start(self) == 
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "l1"]
    /\ UNCHANGED << x, y, S >>

l1(self) == 
    /\ pc[self] = "l1"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "l2"]
    /\ UNCHANGED << y, b, S >>

l2(self) == 
    /\ pc[self] = "l2"
    /\ IF y /= 0
        THEN /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "l3"]
        ELSE /\ pc' = [pc EXCEPT ![self] = "l4"]
             /\ b' = b
    /\ UNCHANGED << x, y, S >>

l3(self) == 
    /\ pc[self] = "l3"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, S >>

l4(self) == 
    /\ pc[self] = "l4"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "l5"]
    /\ UNCHANGED << x, b, S >>

l5(self) == 
    /\ pc[self] = "l5"
    /\ IF x /= self
        THEN /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "l6"]
        ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ b' = b
    /\ UNCHANGED << x, y, S >>

l6(self) == 
    /\ pc[self] = "l6"
    /\ S' = [S EXCEPT ![self] = Procs \ {self}]
    /\ pc' = [pc EXCEPT ![self] = "l7"]
    /\ UNCHANGED << x, y, b >>

l7(self) == 
    /\ pc[self] = "l7"
    /\ IF S[self] /= {}
        THEN /\ \E p \in S[self]:
                /\ ~b[p]
                /\ S' = [S EXCEPT ![self] = S[self] \ {p}]
             /\ pc' = [pc EXCEPT ![self] = "l7"]
        ELSE /\ pc' = [pc EXCEPT ![self] = "l8"]
             /\ S' = S
    /\ UNCHANGED << x, y, b >>

l8(self) == 
    /\ pc[self] = "l8"
    /\ IF y /= self
        THEN /\ pc' = [pc EXCEPT ![self] = "l9"]
        ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, S >>

l9(self) == 
    /\ pc[self] = "l9"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, S >>

cs(self) == 
    /\ pc[self] = "cs"
    /\ TRUE
    /\ pc' = [pc EXCEPT ![self] = "l10"]
    /\ UNCHANGED << x, y, b, S >>

l10(self) == 
    /\ pc[self] = "l10"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, S >>

proc(self) == 
    \/ start(self) 
    \/ l1(self) 
    \/ l2(self) 
    \/ l3(self) 
    \/ l4(self) 
    \/ l5(self) 
    \/ l6(self) 
    \/ l7(self) 
    \/ l8(self) 
    \/ l9(self) 
    \/ cs(self) 
    \/ l10(self)

Next == (\E self \in Procs: proc(self))

Spec == Init /\ [][Next]_vars /\ \A self \in Procs: WF_vars(proc(self))

\* Safety: Mutual Exclusion
Invariant == \A i, j \in Procs : (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Liveness: Infinitely often some process is in the critical section
Liveness == []<>(\E self \in Procs : pc[self] = "cs")

==========================================================================