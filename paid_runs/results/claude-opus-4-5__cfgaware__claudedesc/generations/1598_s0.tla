---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES x, y, b, pc, S

vars == <<x, y, b, pc, S>>

Procs == 1..N

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "start"]
    /\ S = [i \in Procs |-> {}]

Start(self) ==
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "setx"]
    /\ UNCHANGED <<x, y, S>>

SetX(self) ==
    /\ pc[self] = "setx"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "checky1"]
    /\ UNCHANGED <<y, b, S>>

CheckY1(self) ==
    /\ pc[self] = "checky1"
    /\ IF y /= 0
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "waity1"]
            /\ UNCHANGED <<x, y, S>>
       ELSE /\ pc' = [pc EXCEPT ![self] = "sety"]
            /\ UNCHANGED <<x, y, b, S>>

WaitY1(self) ==
    /\ pc[self] = "waity1"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, S>>

SetY(self) ==
    /\ pc[self] = "sety"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "checkx"]
    /\ UNCHANGED <<x, b, S>>

CheckX(self) ==
    /\ pc[self] = "checkx"
    /\ IF x /= self
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ S' = [S EXCEPT ![self] = Procs \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "waitflags"]
            /\ UNCHANGED <<x, y>>
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED <<x, y, b, S>>

WaitFlags(self) ==
    /\ pc[self] = "waitflags"
    /\ IF S[self] /= {}
       THEN \E j \in S[self]:
            /\ b[j] = FALSE
            /\ S' = [S EXCEPT ![self] = S[self] \ {j}]
            /\ pc' = [pc EXCEPT ![self] = "waitflags"]
            /\ UNCHANGED <<x, y, b>>
       ELSE /\ pc' = [pc EXCEPT ![self] = "checky2"]
            /\ UNCHANGED <<x, y, b, S>>

CheckY2(self) ==
    /\ pc[self] = "checky2"
    /\ IF y /= self
       THEN /\ pc' = [pc EXCEPT ![self] = "waity2"]
            /\ UNCHANGED <<x, y, b, S>>
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED <<x, y, b, S>>

WaitY2(self) ==
    /\ pc[self] = "waity2"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, S>>

CS(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<x, y, b, S>>

Exit(self) ==
    /\ pc[self] = "exit"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, S>>

Step(self) ==
    \/ Start(self)
    \/ SetX(self)
    \/ CheckY1(self)
    \/ WaitY1(self)
    \/ SetY(self)
    \/ CheckX(self)
    \/ WaitFlags(self)
    \/ CheckY2(self)
    \/ WaitY2(self)
    \/ CS(self)
    \/ Exit(self)

Next == \E self \in Procs: Step(self)

Fairness == \A self \in Procs: WF_vars(Step(self))

Spec == Init /\ [][Next]_vars /\ Fairness

Invariant ==
    \A i, j \in Procs: (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Liveness == []<>(\E i \in Procs: pc[i] = "cs")

==========================================================================