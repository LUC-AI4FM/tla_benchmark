---------------------------- MODULE FastMutex2 ----------------------------
EXTENDS Integers, TLAPS

CONSTANTS N, M

Proc1 == 1..M
Proc2 == (M+1)..N
Procs == Proc1 \cup Proc2

VARIABLES x, y, b, pc, c1, unchecked1, fail1, c2, unchecked2, fail2

vars == <<x, y, b, pc, c1, unchecked1, fail1, c2, unchecked2, fail2>>

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "start"]
    /\ c1 = [i \in Proc1 |-> 0]
    /\ unchecked1 = [i \in Proc1 |-> {}]
    /\ fail1 = [i \in Proc1 |-> FALSE]
    /\ c2 = [i \in Proc2 |-> 0]
    /\ unchecked2 = [i \in Proc2 |-> {}]
    /\ fail2 = [i \in Proc2 |-> FALSE]

(* Process type 1 actions *)

start1(self) ==
    /\ self \in Proc1
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "checkY"]
    /\ UNCHANGED <<y, c1, unchecked1, fail1, c2, unchecked2, fail2>>

checkY1(self) ==
    /\ self \in Proc1
    /\ pc[self] = "checkY"
    /\ IF y /= 0
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "waitY1"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "setY"]
            /\ b' = b
    /\ UNCHANGED <<x, y, c1, unchecked1, fail1, c2, unchecked2, fail2>>

waitY1_1(self) ==
    /\ self \in Proc1
    /\ pc[self] = "waitY1"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, c1, unchecked1, fail1, c2, unchecked2, fail2>>

setY1(self) ==
    /\ self \in Proc1
    /\ pc[self] = "setY"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "checkX"]
    /\ UNCHANGED <<x, b, c1, unchecked1, fail1, c2, unchecked2, fail2>>

checkX1(self) ==
    /\ self \in Proc1
    /\ pc[self] = "checkX"
    /\ IF x /= self
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ unchecked1' = [unchecked1 EXCEPT ![self] = Procs \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "waitFlags"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ b' = b
            /\ unchecked1' = unchecked1
    /\ UNCHANGED <<x, y, c1, fail1, c2, unchecked2, fail2>>

waitFlags1(self) ==
    /\ self \in Proc1
    /\ pc[self] = "waitFlags"
    /\ IF unchecked1[self] /= {}
       THEN /\ \E j \in unchecked1[self]:
                 /\ b[j] = FALSE
                 /\ unchecked1' = [unchecked1 EXCEPT ![self] = unchecked1[self] \ {j}]
            /\ pc' = [pc EXCEPT ![self] = "waitFlags"]
            /\ fail1' = fail1
       ELSE /\ pc' = [pc EXCEPT ![self] = "checkY2"]
            /\ unchecked1' = unchecked1
            /\ fail1' = fail1
    /\ UNCHANGED <<x, y, b, c1, c2, unchecked2, fail2>>

checkY2_1(self) ==
    /\ self \in Proc1
    /\ pc[self] = "checkY2"
    /\ IF y /= self
       THEN /\ fail1' = [fail1 EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "waitY2"]
       ELSE /\ fail1' = [fail1 EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED <<x, y, b, c1, unchecked1, c2, unchecked2, fail2>>

waitY2_1(self) ==
    /\ self \in Proc1
    /\ pc[self] = "waitY2"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ fail1' = [fail1 EXCEPT ![self] = FALSE]
    /\ UNCHANGED <<x, y, b, c1, unchecked1, c2, unchecked2, fail2>>

cs1(self) ==
    /\ self \in Proc1
    /\ pc[self] = "cs"
    /\ ~fail1[self]
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<x, y, b, c1, unchecked1, fail1, c2, unchecked2, fail2>>

exit1(self) ==
    /\ self \in Proc1
    /\ pc[self] = "exit"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, c1, unchecked1, fail1, c2, unchecked2, fail2>>

(* Process type 2 actions *)

start2(self) ==
    /\ self \in Proc2
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "checkY"]
    /\ UNCHANGED <<y, c1, unchecked1, fail1, c2, unchecked2, fail2>>

checkY2(self) ==
    /\ self \in Proc2
    /\ pc[self] = "checkY"
    /\ IF y /= 0
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "waitY1"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "setY"]
            /\ b' = b
    /\ UNCHANGED <<x, y, c1, unchecked1, fail1, c2, unchecked2, fail2>>

waitY1_2(self) ==
    /\ self \in Proc2
    /\ pc[self] = "waitY1"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, c1, unchecked1, fail1, c2, unchecked2, fail2>>

setY2(self) ==
    /\ self \in Proc2
    /\ pc[self] = "setY"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "checkX"]
    /\ UNCHANGED <<x, b, c1, unchecked1, fail1, c2, unchecked2, fail2>>

checkX2(self) ==
    /\ self \in Proc2
    /\ pc[self] = "checkX"
    /\ IF x /= self
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ unchecked2' = [unchecked2 EXCEPT ![self] = Procs \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "waitFlags"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ b' = b
            /\ unchecked2' = unchecked2
    /\ UNCHANGED <<x, y, c1, unchecked1, fail1, c2, fail2>>

waitFlags2(self) ==
    /\ self \in Proc2
    /\ pc[self] = "waitFlags"
    /\ IF unchecked2[self] /= {}
       THEN /\ \E j \in unchecked2[self]:
                 /\ b[j] = FALSE
                 /\ unchecked2' = [unchecked2 EXCEPT ![self] = unchecked2[self] \ {j}]
            /\ pc' = [pc EXCEPT ![self] = "waitFlags"]
            /\ fail2' = fail2
       ELSE /\ pc' = [pc EXCEPT ![self] = "checkY2"]
            /\ unchecked2' = unchecked2
            /\ fail2' = fail2
    /\ UNCHANGED <<x, y, b, c1, unchecked1, fail1, c2>>

checkY2_2(self) ==
    /\ self \in Proc2
    /\ pc[self] = "checkY2"
    /\ IF y /= self
       THEN /\ fail2' = [fail2 EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "waitY2"]
       ELSE /\ fail2' = [fail2 EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED <<x, y, b, c1, unchecked1, fail1, c2, unchecked2>>

waitY2_2(self) ==
    /\ self \in Proc2
    /\ pc[self] = "waitY2"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ fail2' = [fail2 EXCEPT ![self] = FALSE]
    /\ UNCHANGED <<x, y, b, c1, unchecked1, fail1, c2, unchecked2>>

cs2(self) ==
    /\ self \in Proc2
    /\ pc[self] = "cs"
    /\ ~fail2[self]
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<x, y, b, c1, unchecked1, fail1, c2, unchecked2, fail2>>

exit2(self) ==
    /\ self \in Proc2
    /\ pc[self] = "exit"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, c1, unchecked1, fail1, c2, unchecked2, fail2>>

(* Combined next-state relation *)

Next ==
    \/ \E self \in Proc1:
        \/ start1(self)
        \/ checkY1(self)
        \/ waitY1_1(self)
        \/ setY1(self)
        \/ checkX1(self)
        \/ waitFlags1(self)
        \/ checkY2_1(self)
        \/ waitY2_1(self)
        \/ cs1(self)
        \/ exit1(self)
    \/ \E self \in Proc2:
        \/ start2(self)
        \/ checkY2(self)
        \/ waitY1_2(self)
        \/ setY2(self)
        \/ checkX2(self)
        \/ waitFlags2(self)
        \/ checkY2_2(self)
        \/ waitY2_2(self)
        \/ cs2(self)
        \/ exit2(self)

proc1(self) ==
    \/ start1(self)
    \/ checkY1(self)
    \/ waitY1_1(self)
    \/ setY1(self)
    \/ checkX1(self)
    \/ waitFlags1(self)
    \/ checkY2_1(self)
    \/ waitY2_1(self)
    \/ cs1(self)
    \/ exit1(self)

proc2(self) ==
    \/ start2(self)
    \/ checkY2(self)
    \/ waitY1_2(self)
    \/ setY2(self)
    \/ checkX2(self)
    \/ waitFlags2(self)
    \/ checkY2_2(self)
    \/ waitY2_2(self)
    \/ cs2(self)
    \/ exit2(self)

Fairness ==
    /\ \A self \in Proc1: WF_vars(proc1(self))
    /\ \A self \in Proc2: WF_vars(proc2(self))

Spec == Init /\ [][Next]_vars /\ Fairness

(* A process is in the critical section if it's at "cs" or "exit" label with fail flag clear *)
InCS1(self) == pc[self] \in {"cs", "exit"} /\ ~fail1[self]
InCS2(self) == pc[self] \in {"cs", "exit"} /\ ~fail2[self]

Invariant ==
    \A i, j \in Procs:
        i /= j =>
            ~(/\ (i \in Proc1 => InCS1(i))
              /\ (i \in Proc2 => InCS2(i))
              /\ (j \in Proc1 => InCS1(j))
              /\ (j \in Proc2 => InCS2(j)))

Liveness ==
    \/ <>(\E self \in Proc1: pc[self] = "cs" /\ ~fail1[self])
    \/ <>(\E self \in Proc2: pc[self] = "cs" /\ ~fail2[self])

=============================================================================