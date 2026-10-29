--------------------------- MODULE FastMutex ---------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

ProcSet == 1..N

(***************************************************************************
--algorithm FastMutex {
  variables x = 0, y = 0, b = [i \in 1..N |-> FALSE];
  process (Proc \in 1..N)
    variable S = {};
  {
  ncs:   while (TRUE) {
           skip;  \* noncritical section
  start:   b[self] := TRUE;
  l1:      x := self;
  l2:      if (y # 0) {
  l3:        b[self] := FALSE;
  l4:        await y = 0;
             goto start
           };
  l5:      y := self;
  l6:      if (x # self) {
  l7:        b[self] := FALSE;
             S := ProcSet \ {self};
  l8:        while (S # {}) {
               with (j \in S) {
                 await ~b[j];
                 S := S \ {j}
               }
             };
  l9:        if (y # self) {
  l10:         await y = 0;
               goto start
             }
           };
  cs:      skip;  \* critical section
  l11:     y := 0;
  l12:     b[self] := FALSE
         }
  }
}
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES x, y, b, pc, S

vars == << x, y, b, pc, S >>

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ S = [self \in ProcSet |-> {}]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, S >>

start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "l1"]
               /\ UNCHANGED << x, y, S >>

l1(self) == /\ pc[self] = "l1"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << y, b, S >>

l2(self) == /\ pc[self] = "l2"
            /\ IF y # 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "l3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << x, y, b, S >>

l3(self) == /\ pc[self] = "l3"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ UNCHANGED << x, y, S >>

l4(self) == /\ pc[self] = "l4"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, S >>

l5(self) == /\ pc[self] = "l5"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "l6"]
            /\ UNCHANGED << x, b, S >>

l6(self) == /\ pc[self] = "l6"
            /\ IF x # self
                  THEN /\ pc' = [pc EXCEPT ![self] = "l7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, S >>

l7(self) == /\ pc[self] = "l7"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ S' = [S EXCEPT ![self] = ProcSet \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "l8"]
            /\ UNCHANGED << x, y >>

l8(self) == /\ pc[self] = "l8"
            /\ IF S[self] # {}
                  THEN /\ \E j \in S[self]:
                            /\ ~b[j]
                            /\ S' = [S EXCEPT ![self] = S[self] \ {j}]
                       /\ pc' = [pc EXCEPT ![self] = "l8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l9"]
                       /\ S' = S
            /\ UNCHANGED << x, y, b >>

l9(self) == /\ pc[self] = "l9"
            /\ IF y # self
                  THEN /\ pc' = [pc EXCEPT ![self] = "l10"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, S >>

l10(self) == /\ pc[self] = "l10"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, S >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l11"]
            /\ UNCHANGED << x, y, b, S >>

l11(self) == /\ pc[self] = "l11"
             /\ y' = 0
             /\ pc' = [pc EXCEPT ![self] = "l12"]
             /\ UNCHANGED << x, b, S >>

l12(self) == /\ pc[self] = "l12"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << x, y, S >>

Proc(self) == ncs(self) \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self)
                 \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self)
                 \/ l8(self) \/ l9(self) \/ l10(self) \/ cs(self)
                 \/ l11(self) \/ l12(self)

Next == (\E self \in 1..N: Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
\* END TRANSLATION

TypeOK == /\ x \in 0..N
          /\ y \in 0..N
          /\ b \in [1..N -> BOOLEAN]
          /\ S \in [ProcSet -> SUBSET ProcSet]
          /\ pc \in [ProcSet -> {"ncs", "start", "l1", "l2", "l3", "l4", "l5",
                                 "l6", "l7", "l8", "l9", "l10", "cs",
                                 "l11", "l12"}]

Mutex == \A i, j \in ProcSet : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Liveness == []<>(\E i \in ProcSet : pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ Mutex)
THEOREM Spec => Liveness
=============================================================================