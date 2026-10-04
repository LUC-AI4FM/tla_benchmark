------------------------------ MODULE FastMutex2 ------------------------------
EXTENDS Integers, TLAPS

CONSTANTS N, M

ASSUME NMConstraint == /\ N \in Nat \ {0}
                       /\ M \in Nat \ {0}
                       /\ M < N

Proc1 == 1..M
Proc2 == (M+1)..N
Procs == Proc1 \cup Proc2

VARIABLES x, y, b, pc1, pc2, j1, j2, failed1, failed2

vars == <<x, y, b, pc1, pc2, j1, j2, failed1, failed2>>

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in Procs |-> FALSE]
        /\ pc1 = [i \in Proc1 |-> "start"]
        /\ pc2 = [i \in Proc2 |-> "start"]
        /\ j1 = [i \in Proc1 |-> 1]
        /\ j2 = [i \in Proc2 |-> M+1]
        /\ failed1 = [i \in Proc1 |-> FALSE]
        /\ failed2 = [i \in Proc2 |-> FALSE]

(* Proc1 actions *)

start1(self) == 
    /\ pc1[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ x' = self
    /\ pc1' = [pc1 EXCEPT ![self] = "checkY"]
    /\ UNCHANGED <<y, pc2, j1, j2, failed1, failed2>>

checkY1(self) ==
    /\ pc1[self] = "checkY"
    /\ IF y /= 0
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc1' = [pc1 EXCEPT ![self] = "waitY1"]
            /\ UNCHANGED <<x, y, j1, failed1>>
       ELSE /\ pc1' = [pc1 EXCEPT ![self] = "setY"]
            /\ UNCHANGED <<x, y, b, j1, failed1>>
    /\ UNCHANGED <<pc2, j2, failed2>>

waitY1_1(self) ==
    /\ pc1[self] = "waitY1"
    /\ y = 0
    /\ pc1' = [pc1 EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, pc2, j1, j2, failed1, failed2>>

setY1(self) ==
    /\ pc1[self] = "setY"
    /\ y' = self
    /\ pc1' = [pc1 EXCEPT ![self] = "checkX"]
    /\ UNCHANGED <<x, b, pc2, j1, j2, failed1, failed2>>

checkX1(self) ==
    /\ pc1[self] = "checkX"
    /\ IF x /= self
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ j1' = [j1 EXCEPT ![self] = 1]
            /\ pc1' = [pc1 EXCEPT ![self] = "waitB"]
            /\ UNCHANGED <<x, y, failed1>>
       ELSE /\ pc1' = [pc1 EXCEPT ![self] = "cs"]
            /\ UNCHANGED <<x, y, b, j1, failed1>>
    /\ UNCHANGED <<pc2, j2, failed2>>

waitB1(self) ==
    /\ pc1[self] = "waitB"
    /\ IF j1[self] <= N
       THEN /\ IF b[j1[self]] = FALSE
               THEN /\ j1' = [j1 EXCEPT ![self] = j1[self] + 1]
                    /\ pc1' = [pc1 EXCEPT ![self] = "waitB"]
               ELSE /\ UNCHANGED <<j1, pc1>>
            /\ UNCHANGED <<x, y, b, failed1>>
       ELSE /\ pc1' = [pc1 EXCEPT ![self] = "checkY2"]
            /\ UNCHANGED <<x, y, b, j1, failed1>>
    /\ UNCHANGED <<pc2, j2, failed2>>

checkY2_1(self) ==
    /\ pc1[self] = "checkY2"
    /\ IF y /= self
       THEN /\ failed1' = [failed1 EXCEPT ![self] = TRUE]
            /\ pc1' = [pc1 EXCEPT ![self] = "waitY2"]
            /\ UNCHANGED <<x, y, b>>
       ELSE /\ pc1' = [pc1 EXCEPT ![self] = "cs"]
            /\ UNCHANGED <<x, y, b, failed1>>
    /\ UNCHANGED <<pc2, j1, j2, failed2>>

waitY2_1(self) ==
    /\ pc1[self] = "waitY2"
    /\ y = 0
    /\ pc1' = [pc1 EXCEPT ![self] = "cs"]
    /\ UNCHANGED <<x, y, b, pc2, j1, j2, failed1, failed2>>

cs1(self) ==
    /\ pc1[self] = "cs"
    /\ IF failed1[self] = FALSE
       THEN /\ pc1' = [pc1 EXCEPT ![self] = "exit"]
            /\ UNCHANGED <<x, y, b, failed1>>
       ELSE /\ failed1' = [failed1 EXCEPT ![self] = FALSE]
            /\ pc1' = [pc1 EXCEPT ![self] = "start"]
            /\ UNCHANGED <<x, y, b>>
    /\ UNCHANGED <<pc2, j1, j2, failed2>>

exit1(self) ==
    /\ pc1[self] = "exit"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc1' = [pc1 EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, pc2, j1, j2, failed1, failed2>>

proc1(self) ==
    \/ start1(self)
    \/ checkY1(self)
    \/ waitY1_1(self)
    \/ setY1(self)
    \/ checkX1(self)
    \/ waitB1(self)
    \/ checkY2_1(self)
    \/ waitY2_1(self)
    \/ cs1(self)
    \/ exit1(self)

(* Proc2 actions *)

start2(self) == 
    /\ pc2[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ x' = self
    /\ pc2' = [pc2 EXCEPT ![self] = "checkY"]
    /\ UNCHANGED <<y, pc1, j1, j2, failed1, failed2>>

checkY2(self) ==
    /\ pc2[self] = "checkY"
    /\ IF y /= 0
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc2' = [pc2 EXCEPT ![self] = "waitY1"]
            /\ UNCHANGED <<x, y, j2, failed2>>
       ELSE /\ pc2' = [pc2 EXCEPT ![self] = "setY"]
            /\ UNCHANGED <<x, y, b, j2, failed2>>
    /\ UNCHANGED <<pc1, j1, failed1>>

waitY1_2(self) ==
    /\ pc2[self] = "waitY1"
    /\ y = 0
    /\ pc2' = [pc2 EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, pc1, j1, j2, failed1, failed2>>

setY2(self) ==
    /\ pc2[self] = "setY"
    /\ y' = self
    /\ pc2' = [pc2 EXCEPT ![self] = "checkX"]
    /\ UNCHANGED <<x, b, pc1, j1, j2, failed1, failed2>>

checkX2(self) ==
    /\ pc2[self] = "checkX"
    /\ IF x /= self
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ j2' = [j2 EXCEPT ![self] = 1]
            /\ pc2' = [pc2 EXCEPT ![self] = "waitB"]
            /\ UNCHANGED <<x, y, failed2>>
       ELSE /\ pc2' = [pc2 EXCEPT ![self] = "cs"]
            /\ UNCHANGED <<x, y, b, j2, failed2>>
    /\ UNCHANGED <<pc1, j1, failed1>>

waitB2(self) ==
    /\ pc2[self] = "waitB"
    /\ IF j2[self] <= N
       THEN /\ IF b[j2[self]] = FALSE
               THEN /\ j2' = [j2 EXCEPT ![self] = j2[self] + 1]
                    /\ pc2' = [pc2 EXCEPT ![self] = "waitB"]
               ELSE /\ UNCHANGED <<j2, pc2>>
            /\ UNCHANGED <<x, y, b, failed2>>
       ELSE /\ pc2' = [pc2 EXCEPT ![self] = "checkY2"]
            /\ UNCHANGED <<x, y, b, j2, failed2>>
    /\ UNCHANGED <<pc1, j1, failed1>>

checkY2_2(self) ==
    /\ pc2[self] = "checkY2"
    /\ IF y /= self
       THEN /\ failed2' = [failed2 EXCEPT ![self] = TRUE]
            /\ pc2' = [pc2 EXCEPT ![self] = "waitY2"]
            /\ UNCHANGED <<x, y, b>>
       ELSE /\ pc2' = [pc2 EXCEPT ![self] = "cs"]
            /\ UNCHANGED <<x, y, b, failed2>>
    /\ UNCHANGED <<pc1, j1, j2, failed1>>

waitY2_2(self) ==
    /\ pc2[self] = "waitY2"
    /\ y = 0
    /\ pc2' = [pc2 EXCEPT ![self] = "cs"]
    /\ UNCHANGED <<x, y, b, pc1, j1, j2, failed1, failed2>>

cs2(self) ==
    /\ pc2[self] = "cs"
    /\ IF failed2[self] = FALSE
       THEN /\ pc2' = [pc2 EXCEPT ![self] = "exit"]
            /\ UNCHANGED <<x, y, b, failed2>>
       ELSE /\ failed2' = [failed2 EXCEPT ![self] = FALSE]
            /\ pc2' = [pc2 EXCEPT ![self] = "start"]
            /\ UNCHANGED <<x, y, b>>
    /\ UNCHANGED <<pc1, j1, j2, failed1>>

exit2(self) ==
    /\ pc2[self] = "exit"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc2' = [pc2 EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, pc1, j1, j2, failed1, failed2>>

proc2(self) ==
    \/ start2(self)
    \/ checkY2(self)
    \/ waitY1_2(self)
    \/ setY2(self)
    \/ checkX2(self)
    \/ waitB2(self)
    \/ checkY2_2(self)
    \/ waitY2_2(self)
    \/ cs2(self)
    \/ exit2(self)

Next == \/ \E self \in Proc1: proc1(self)
        \/ \E self \in Proc2: proc2(self)

Fairness == /\ \A self \in Proc1: WF_vars(proc1(self))
            /\ \A self \in Proc2: WF_vars(proc2(self))

Spec == Init /\ [][Next]_vars /\ Fairness

(* Safety: Mutual Exclusion *)
InCS1(i) == pc1[i] = "exit" /\ failed1[i] = FALSE
InCS2(i) == pc2[i] = "exit" /\ failed2[i] = FALSE

MutualExclusion ==
    /\ \A i, j \in Proc1: i /= j => ~(InCS1(i) /\ InCS1(j))
    /\ \A i, j \in Proc2: i /= j => ~(InCS2(i) /\ InCS2(j))
    /\ \A i \in Proc1, j \in Proc2: ~(InCS1(i) /\ InCS2(j))

(* Liveness: Some process infinitely often in CS *)
SomeoneInCS == \/ \E i \in Proc1: InCS1(i)
               \/ \E i \in Proc2: InCS2(i)

Liveness == []<>SomeoneInCS

===============================================================================