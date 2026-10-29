------------------------------ MODULE FastMutex ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 1

Procs == 1..N

VARIABLES x, y, b, S, pc

vars == << x, y, b, S, pc >>

TypeOK ==
    /\ x \in Procs \cup {0}
    /\ y \in Procs \cup {0}
    /\ b \in [Procs -> BOOLEAN]
    /\ S \in [Procs -> SUBSET Procs]
    /\ pc \in [Procs -> {"start", "l1", "l2", "l3", "l4", "l5",
                         "l6", "l7", "l8", "cs", "l9"}]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ S = [i \in Procs |-> {}]
    /\ pc = [i \in Procs |-> "start"]

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
    /\ IF y # 0
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
    /\ IF x # self
          THEN /\ b' = [b EXCEPT ![self] = FALSE]
               /\ S' = [S EXCEPT ![self] = Procs \ {self}]
               /\ pc' = [pc EXCEPT ![self] = "l6"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ UNCHANGED << b, S >>
    /\ UNCHANGED << x, y >>

l6(self) ==
    /\ pc[self] = "l6"
    /\ IF S[self] # {}
          THEN /\ \E j \in S[self] :
                    /\ ~b[j]
                    /\ S' = [S EXCEPT ![self] = @ \ {j}]
               /\ pc' = pc
          ELSE /\ pc' = [pc EXCEPT ![self] = "l7"]
               /\ S' = S
    /\ UNCHANGED << x, y, b >>

l7(self) ==
    /\ pc[self] = "l7"
    /\ IF y # self
          THEN pc' = [pc EXCEPT ![self] = "l8"]
          ELSE pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, S >>

l8(self) ==
    /\ pc[self] = "l8"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, S >>

cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "l9"]
    /\ UNCHANGED << x, y, b, S >>

l9(self) ==
    /\ pc[self] = "l9"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, S >>

proc(self) ==
    \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self) \/ l4(self)
    \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self) \/ cs(self) \/ l9(self)

Next == \E self \in Procs : proc(self)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Invariant ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Liveness == []<>(\E i \in Procs : pc[i] = "cs")

=============================================================================