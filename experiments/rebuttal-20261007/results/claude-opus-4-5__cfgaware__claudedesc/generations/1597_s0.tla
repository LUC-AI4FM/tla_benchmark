---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N >= 2

VARIABLES x, y, b, pc, j, failed, j2, failed2

vars == <<x, y, b, pc, j, failed, j2, failed2>>

Procs == 1..N

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in 1..N |-> FALSE]
    /\ pc = [self \in Procs |-> IF self = 1 THEN "start1" ELSE "start2"]
    /\ j = 1
    /\ failed = FALSE
    /\ j2 = [self \in 2..N |-> 1]
    /\ failed2 = [self \in 2..N |-> FALSE]

(* Process 1 actions *)

start1 ==
    /\ pc[1] = "start1"
    /\ b' = [b EXCEPT ![1] = TRUE]
    /\ pc' = [pc EXCEPT ![1] = "setx1"]
    /\ UNCHANGED <<x, y, j, failed, j2, failed2>>

setx1 ==
    /\ pc[1] = "setx1"
    /\ x' = 1
    /\ pc' = [pc EXCEPT ![1] = "checky1"]
    /\ UNCHANGED <<y, b, j, failed, j2, failed2>>

checky1 ==
    /\ pc[1] = "checky1"
    /\ IF y /= 0
       THEN pc' = [pc EXCEPT ![1] = "backoff1"]
       ELSE pc' = [pc EXCEPT ![1] = "sety1"]
    /\ UNCHANGED <<x, y, b, j, failed, j2, failed2>>

backoff1 ==
    /\ pc[1] = "backoff1"
    /\ b' = [b EXCEPT ![1] = FALSE]
    /\ pc' = [pc EXCEPT ![1] = "waity1"]
    /\ UNCHANGED <<x, y, j, failed, j2, failed2>>

waity1 ==
    /\ pc[1] = "waity1"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![1] = "start1"]
    /\ UNCHANGED <<x, y, b, j, failed, j2, failed2>>

sety1 ==
    /\ pc[1] = "sety1"
    /\ y' = 1
    /\ pc' = [pc EXCEPT ![1] = "checkx1"]
    /\ UNCHANGED <<x, b, j, failed, j2, failed2>>

checkx1 ==
    /\ pc[1] = "checkx1"
    /\ IF x /= 1
       THEN /\ b' = [b EXCEPT ![1] = FALSE]
            /\ j' = 1
            /\ pc' = [pc EXCEPT ![1] = "waitloop1"]
       ELSE /\ pc' = [pc EXCEPT ![1] = "cs1"]
            /\ UNCHANGED <<b, j>>
    /\ UNCHANGED <<x, y, failed, j2, failed2>>

waitloop1 ==
    /\ pc[1] = "waitloop1"
    /\ IF j <= N
       THEN pc' = [pc EXCEPT ![1] = "waitb1"]
       ELSE pc' = [pc EXCEPT ![1] = "checky2_1"]
    /\ UNCHANGED <<x, y, b, j, failed, j2, failed2>>

waitb1 ==
    /\ pc[1] = "waitb1"
    /\ IF j /= 1
       THEN /\ b[j] = FALSE
            /\ j' = j + 1
            /\ pc' = [pc EXCEPT ![1] = "waitloop1"]
       ELSE /\ j' = j + 1
            /\ pc' = [pc EXCEPT ![1] = "waitloop1"]
    /\ UNCHANGED <<x, y, b, failed, j2, failed2>>

checky2_1 ==
    /\ pc[1] = "checky2_1"
    /\ IF y /= 1
       THEN /\ failed' = TRUE
            /\ pc' = [pc EXCEPT ![1] = "checkfailed1"]
       ELSE /\ pc' = [pc EXCEPT ![1] = "checkfailed1"]
            /\ UNCHANGED failed
    /\ UNCHANGED <<x, y, b, j, j2, failed2>>

checkfailed1 ==
    /\ pc[1] = "checkfailed1"
    /\ IF failed = FALSE
       THEN pc' = [pc EXCEPT ![1] = "cs1"]
       ELSE /\ pc' = [pc EXCEPT ![1] = "waityfinal1"]
    /\ UNCHANGED <<x, y, b, j, failed, j2, failed2>>

waityfinal1 ==
    /\ pc[1] = "waityfinal1"
    /\ y = 0
    /\ failed' = FALSE
    /\ pc' = [pc EXCEPT ![1] = "start1"]
    /\ UNCHANGED <<x, y, b, j, j2, failed2>>

cs1 ==
    /\ pc[1] = "cs1"
    /\ pc' = [pc EXCEPT ![1] = "exit1"]
    /\ UNCHANGED <<x, y, b, j, failed, j2, failed2>>

exit1 ==
    /\ pc[1] = "exit1"
    /\ y' = 0
    /\ b' = [b EXCEPT ![1] = FALSE]
    /\ failed' = FALSE
    /\ pc' = [pc EXCEPT ![1] = "start1"]
    /\ UNCHANGED <<x, j, j2, failed2>>

(* Process 2..N actions *)

start2(self) ==
    /\ self \in 2..N
    /\ pc[self] = "start2"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "setx2"]
    /\ UNCHANGED <<x, y, j, failed, j2, failed2>>

setx2(self) ==
    /\ self \in 2..N
    /\ pc[self] = "setx2"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "checky2"]
    /\ UNCHANGED <<y, b, j, failed, j2, failed2>>

checky2(self) ==
    /\ self \in 2..N
    /\ pc[self] = "checky2"
    /\ IF y /= 0
       THEN pc' = [pc EXCEPT ![self] = "backoff2"]
       ELSE pc' = [pc EXCEPT ![self] = "sety2"]
    /\ UNCHANGED <<x, y, b, j, failed, j2, failed2>>

backoff2(self) ==
    /\ self \in 2..N
    /\ pc[self] = "backoff2"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "waity2"]
    /\ UNCHANGED <<x, y, j, failed, j2, failed2>>

waity2(self) ==
    /\ self \in 2..N
    /\ pc[self] = "waity2"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start2"]
    /\ UNCHANGED <<x, y, b, j, failed, j2, failed2>>

sety2(self) ==
    /\ self \in 2..N
    /\ pc[self] = "sety2"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "checkx2"]
    /\ UNCHANGED <<x, b, j, failed, j2, failed2>>

checkx2(self) ==
    /\ self \in 2..N
    /\ pc[self] = "checkx2"
    /\ IF x /= self
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ j2' = [j2 EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "waitloop2"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs2"]
            /\ UNCHANGED <<b, j2>>
    /\ UNCHANGED <<x, y, j, failed, failed2>>

waitloop2(self) ==
    /\ self \in 2..N
    /\ pc[self] = "waitloop2"
    /\ IF j2[self] <= N
       THEN pc' = [pc EXCEPT ![self] = "waitb2"]
       ELSE pc' = [pc EXCEPT ![self] = "checky2_2"]
    /\ UNCHANGED <<x, y, b, j, failed, j2, failed2>>

waitb2(self) ==
    /\ self \in 2..N
    /\ pc[self] = "waitb2"
    /\ IF j2[self] /= self
       THEN /\ b[j2[self]] = FALSE
            /\ j2' = [j2 EXCEPT ![self] = j2[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "waitloop2"]
       ELSE /\ j2' = [j2 EXCEPT ![self] = j2[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "waitloop2"]
    /\ UNCHANGED <<x, y, b, j, failed, failed2>>

checky2_2(self) ==
    /\ self \in 2..N
    /\ pc[self] = "checky2_2"
    /\ IF y /= self
       THEN /\ failed2' = [failed2 EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "checkfailed2"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "checkfailed2"]
            /\ UNCHANGED failed2
    /\ UNCHANGED <<x, y, b, j, failed, j2>>

checkfailed2(self) ==
    /\ self \in 2..N
    /\ pc[self] = "checkfailed2"
    /\ IF failed2[self] = FALSE
       THEN pc' = [pc EXCEPT ![self] = "cs2"]
       ELSE pc' = [pc EXCEPT ![self] = "waityfinal2"]
    /\ UNCHANGED <<x, y, b, j, failed, j2, failed2>>

waityfinal2(self) ==
    /\ self \in 2..N
    /\ pc[self] = "waityfinal2"
    /\ y = 0
    /\ failed2' = [failed2 EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "start2"]
    /\ UNCHANGED <<x, y, b, j, failed, j2>>

cs2(self) ==
    /\ self \in 2..N
    /\ pc[self] = "cs2"
    /\ pc' = [pc EXCEPT ![self] = "exit2"]
    /\ UNCHANGED <<x, y, b, j, failed, j2, failed2>>

exit2(self) ==
    /\ self \in 2..N
    /\ pc[self] = "exit2"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ failed2' = [failed2 EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "start2"]
    /\ UNCHANGED <<x, j, failed, j2>>

(* Combined next-state relation *)

Proc1Actions ==
    \/ start1
    \/ setx1
    \/ checky1
    \/ backoff1
    \/ waity1
    \/ sety1
    \/ checkx1
    \/ waitloop1
    \/ waitb1
    \/ checky2_1
    \/ checkfailed1
    \/ waityfinal1
    \/ cs1
    \/ exit1

Proc2Actions(self) ==
    \/ start2(self)
    \/ setx2(self)
    \/ checky2(self)
    \/ backoff2(self)
    \/ waity2(self)
    \/ sety2(self)
    \/ checkx2(self)
    \/ waitloop2(self)
    \/ waitb2(self)
    \/ checky2_2(self)
    \/ checkfailed2(self)
    \/ waityfinal2(self)
    \/ cs2(self)
    \/ exit2(self)

Next ==
    \/ Proc1Actions
    \/ \E self \in 2..N : Proc2Actions(self)

(* Fairness conditions *)

Fairness ==
    /\ WF_vars(Proc1Actions)
    /\ \A self \in 2..N : WF_vars(Proc2Actions(self))

(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

(* Invariant: Mutual Exclusion *)

InCS(p) ==
    IF p = 1 THEN pc[1] = "cs1" ELSE pc[p] = "cs2"

Invariant ==
    \A p1, p2 \in Procs : (p1 /= p2) => ~(InCS(p1) /\ InCS(p2))

(* Liveness: Some process is infinitely often in the critical section *)

Liveness ==
    []<>(\E p \in Procs : InCS(p))

=============================================================================