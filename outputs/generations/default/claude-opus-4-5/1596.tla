---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, TLAPS

CONSTANTS M, N

ASSUME MN == /\ M \in Nat \ {0}
            /\ N \in Nat
            /\ M < N

Procs1 == 1..M
Procs2 == (M+1)..N
Procs == Procs1 \cup Procs2

(*
--algorithm FastMutex {
    variables x = 0, y = 0, b = [i \in Procs |-> FALSE];
    
    fair process (P1 \in Procs1)
    variable j = 0;
    {
    start1:
        b[self] := TRUE;
    setx1:
        x := self;
    checkx1:
        if (y # 0) {
            b[self] := FALSE;
        await1:
            await y = 0;
            goto start1;
        };
    sety1:
        y := self;
    checky1:
        if (x # self) {
            b[self] := FALSE;
        wait1:
            j := 1;
        waitloop1:
            while (j <= N) {
                await ~b[j];
                j := j + 1;
            };
        checkfinal1:
            if (y # self) {
            awaity1:
                await y = 0;
                goto start1;
            };
        };
    cs1:
        skip;
    exit1:
        y := 0;
        b[self] := FALSE;
        goto start1;
    }
    
    fair process (P2 \in Procs2)
    variable k = 0;
    {
    start2:
        b[self] := TRUE;
    setx2:
        x := self;
    checkx2:
        if (y # 0) {
            b[self] := FALSE;
        await2:
            await y = 0;
            goto start2;
        };
    sety2:
        y := self;
    checky2:
        if (x # self) {
            b[self] := FALSE;
        wait2:
            k := 1;
        waitloop2:
            while (k <= N) {
                await ~b[k];
                k := k + 1;
            };
        checkfinal2:
            if (y # self) {
            awaity2:
                await y = 0;
                goto start2;
            };
        };
    cs2:
        skip;
    exit2:
        y := 0;
        b[self] := FALSE;
        goto start2;
    }
}
*)

\* BEGIN TRANSLATION
VARIABLES x, y, b, pc, j, k

vars == << x, y, b, pc, j, k >>

ProcSet == (Procs1) \cup (Procs2)

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ b = [i \in Procs |-> FALSE]
        (* Process P1 *)
        /\ j = [self \in Procs1 |-> 0]
        (* Process P2 *)
        /\ k = [self \in Procs2 |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Procs1 -> "start1"
                                        [] self \in Procs2 -> "start2"]

start1(self) == /\ pc[self] = "start1"
                /\ b' = [b EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "setx1"]
                /\ UNCHANGED << x, y, j, k >>

setx1(self) == /\ pc[self] = "setx1"
               /\ x' = self
               /\ pc' = [pc EXCEPT ![self] = "checkx1"]
               /\ UNCHANGED << y, b, j, k >>

checkx1(self) == /\ pc[self] = "checkx1"
                 /\ IF y # 0
                       THEN /\ b' = [b EXCEPT ![self] = FALSE]
                            /\ pc' = [pc EXCEPT ![self] = "await1"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "sety1"]
                            /\ b' = b
                 /\ UNCHANGED << x, y, j, k >>

await1(self) == /\ pc[self] = "await1"
                /\ y = 0
                /\ pc' = [pc EXCEPT ![self] = "start1"]
                /\ UNCHANGED << x, y, b, j, k >>

sety1(self) == /\ pc[self] = "sety1"
               /\ y' = self
               /\ pc' = [pc EXCEPT ![self] = "checky1"]
               /\ UNCHANGED << x, b, j, k >>

checky1(self) == /\ pc[self] = "checky1"
                 /\ IF x # self
                       THEN /\ b' = [b EXCEPT ![self] = FALSE]
                            /\ pc' = [pc EXCEPT ![self] = "wait1"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "cs1"]
                            /\ b' = b
                 /\ UNCHANGED << x, y, j, k >>

wait1(self) == /\ pc[self] = "wait1"
               /\ j' = [j EXCEPT ![self] = 1]
               /\ pc' = [pc EXCEPT ![self] = "waitloop1"]
               /\ UNCHANGED << x, y, b, k >>

waitloop1(self) == /\ pc[self] = "waitloop1"
                   /\ IF j[self] <= N
                         THEN /\ ~b[j[self]]
                              /\ j' = [j EXCEPT ![self] = j[self] + 1]
                              /\ pc' = [pc EXCEPT ![self] = "waitloop1"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "checkfinal1"]
                              /\ j' = j
                   /\ UNCHANGED << x, y, b, k >>

checkfinal1(self) == /\ pc[self] = "checkfinal1"
                     /\ IF y # self
                           THEN /\ pc' = [pc EXCEPT ![self] = "awaity1"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "cs1"]
                     /\ UNCHANGED << x, y, b, j, k >>

awaity1(self) == /\ pc[self] = "awaity1"
                 /\ y = 0
                 /\ pc' = [pc EXCEPT ![self] = "start1"]
                 /\ UNCHANGED << x, y, b, j, k >>

cs1(self) == /\ pc[self] = "cs1"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "exit1"]
             /\ UNCHANGED << x, y, b, j, k >>

exit1(self) == /\ pc[self] = "exit1"
               /\ y' = 0
               /\ b' = [b EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "start1"]
               /\ UNCHANGED << x, j, k >>

P1(self) == start1(self) \/ setx1(self) \/ checkx1(self) \/ await1(self)
               \/ sety1(self) \/ checky1(self) \/ wait1(self)
               \/ waitloop1(self) \/ checkfinal1(self) \/ awaity1(self)
               \/ cs1(self) \/ exit1(self)

start2(self) == /\ pc[self] = "start2"
                /\ b' = [b EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "setx2"]
                /\ UNCHANGED << x, y, j, k >>

setx2(self) == /\ pc[self] = "setx2"
               /\ x' = self
               /\ pc' = [pc EXCEPT ![self] = "checkx2"]
               /\ UNCHANGED << y, b, j, k >>

checkx2(self) == /\ pc[self] = "checkx2"
                 /\ IF y # 0
                       THEN /\ b' = [b EXCEPT ![self] = FALSE]
                            /\ pc' = [pc EXCEPT ![self] = "await2"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "sety2"]
                            /\ b' = b
                 /\ UNCHANGED << x, y, j, k >>

await2(self) == /\ pc[self] = "await2"
                /\ y = 0
                /\ pc' = [pc EXCEPT ![self] = "start2"]
                /\ UNCHANGED << x, y, b, j, k >>

sety2(self) == /\ pc[self] = "sety2"
               /\ y' = self
               /\ pc' = [pc EXCEPT ![self] = "checky2"]
               /\ UNCHANGED << x, b, j, k >>

checky2(self) == /\ pc[self] = "checky2"
                 /\ IF x # self
                       THEN /\ b' = [b EXCEPT ![self] = FALSE]
                            /\ pc' = [pc EXCEPT ![self] = "wait2"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "cs2"]
                            /\ b' = b
                 /\ UNCHANGED << x, y, j, k >>

wait2(self) == /\ pc[self] = "wait2"
               /\ k' = [k EXCEPT ![self] = 1]
               /\ pc' = [pc EXCEPT ![self] = "waitloop2"]
               /\ UNCHANGED << x, y, b, j >>

waitloop2(self) == /\ pc[self] = "waitloop2"
                   /\ IF k[self] <= N
                         THEN /\ ~b[k[self]]
                              /\ k' = [k EXCEPT ![self] = k[self] + 1]
                              /\ pc' = [pc EXCEPT ![self] = "waitloop2"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "checkfinal2"]
                              /\ k' = k
                   /\ UNCHANGED << x, y, b, j >>

checkfinal2(self) == /\ pc[self] = "checkfinal2"
                     /\ IF y # self
                           THEN /\ pc' = [pc EXCEPT ![self] = "awaity2"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "cs2"]
                     /\ UNCHANGED << x, y, b, j, k >>

awaity2(self) == /\ pc[self] = "awaity2"
                 /\ y = 0
                 /\ pc' = [pc EXCEPT ![self] = "start2"]
                 /\ UNCHANGED << x, y, b, j, k >>

cs2(self) == /\ pc[self] = "cs2"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "exit2"]
             /\ UNCHANGED << x, y, b, j, k >>

exit2(self) == /\ pc[self] = "exit2"
               /\ y' = 0
               /\ b' = [b EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "start2"]
               /\ UNCHANGED << x, j, k >>

P2(self) == start2(self) \/ setx2(self) \/ checkx2(self) \/ await2(self)
               \/ sety2(self) \/ checky2(self) \/ wait2(self)
               \/ waitloop2(self) \/ checkfinal2(self) \/ awaity2(self)
               \/ cs2(self) \/ exit2(self)

Next == (\E self \in Procs1: P1(self))
           \/ (\E self \in Procs2: P2(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs1 : WF_vars(P1(self))
        /\ \A self \in Procs2 : WF_vars(P2(self))

\* END TRANSLATION

-----------------------------------------------------------------------------
(* Safety: Mutual Exclusion *)
InCS(p) == pc[p] \in {"cs1", "cs2"}

MutualExclusion == \A p, q \in Procs : (p # q) => ~(InCS(p) /\ InCS(q))

(* Liveness: Some process enters the critical section infinitely often *)
SomeoneInCS == \E p \in Procs : InCS(p)

Liveness == []<>SomeoneInCS

=============================================================================