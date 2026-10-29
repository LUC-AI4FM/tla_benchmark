------------------------------- MODULE FastMutex -------------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 1

(***************************************************************************
--algorithm FastMutex {
  variables x = 0, y = 0, b = [i \in 1..N |-> FALSE];

  process (Proc1 = 1)
    variables j1 = 1, failed1 = FALSE;
  {
  ncs1:   while (TRUE) {
            skip;
  start1:   b[1] := TRUE; failed1 := FALSE;
  l11:      x := 1;
  l21:      if (y # 0) { b[1] := FALSE; failed1 := TRUE;
  l31:                   await y = 0;
                         goto start1 };
  l41:      y := 1;
  l51:      if (x # 1) { b[1] := FALSE; j1 := 1;
  l61:                   while (j1 <= N) { await ~b[j1]; j1 := j1 + 1 };
  l71:                   if (y # 1) { failed1 := TRUE;
  l81:                                await y = 0;
                                      goto start1 } };
  cs1:      skip;
  l91:      y := 0;
  l101:     b[1] := FALSE
          }
  }

  process (Proc \in 2..N)
    variables j = 1, failed = FALSE;
  {
  ncs:    while (TRUE) {
            skip;
  start:    b[self] := TRUE; failed := FALSE;
  l1:       x := self;
  l2:       if (y # 0) { b[self] := FALSE; failed := TRUE;
  l3:                    await y = 0;
                         goto start };
  l4:       y := self;
  l5:       if (x # self) { b[self] := FALSE; j := 1;
  l6:                       while (j <= N) { await ~b[j]; j := j + 1 };
  l7:                       if (y # self) { failed := TRUE;
  l8:                                       await y = 0;
                                            goto start } };
  cs:       skip;
  l9:       y := 0;
  l10:      b[self] := FALSE
          }
  }
}
 ***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES x, y, b, pc, j, failed

vars == << x, y, b, pc, j, failed >>

ProcSet == {1} \cup (2..N)

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ j = [self \in ProcSet |-> 1]
        /\ failed = [self \in ProcSet |-> FALSE]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j, failed >>

start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ failed' = [failed EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "l1"]
               /\ UNCHANGED << x, y, j >>

l1(self) == /\ pc[self] = "l1"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << y, b, j, failed >>

l2(self) == /\ pc[self] = "l2"
            /\ IF y # 0
                  THEN /\ b' = [b EXCEPT ![self] = FALSE]
                       /\ failed' = [failed EXCEPT ![self] = TRUE]
                       /\ pc' = [pc EXCEPT ![self] = "l3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l4"]
                       /\ UNCHANGED << b, failed >>
            /\ UNCHANGED << x, y, j >>

l3(self) == /\ pc[self] = "l3"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j, failed >>

l4(self) == /\ pc[self] = "l4"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << x, b, j, failed >>

l5(self) == /\ pc[self] = "l5"
            /\ IF x # self
                  THEN /\ b' = [b EXCEPT ![self] = FALSE]
                       /\ j' = [j EXCEPT ![self] = 1]
                       /\ pc' = [pc EXCEPT ![self] = "l6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED << b, j >>
            /\ UNCHANGED << x, y, failed >>

l6(self) == /\ pc[self] = "l6"
            /\ IF j[self] <= N
                  THEN /\ ~b[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "l6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l7"]
                       /\ UNCHANGED j
            /\ UNCHANGED << x, y, b, failed >>

l7(self) == /\ pc[self] = "l7"
            /\ IF y # self
                  THEN /\ failed' = [failed EXCEPT ![self] = TRUE]
                       /\ pc' = [pc EXCEPT ![self] = "l8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED failed
            /\ UNCHANGED << x, y, b, j >>

l8(self) == /\ pc[self] = "l8"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j, failed >>

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "l9"]
            /\ UNCHANGED << x, y, b, j, failed >>

l9(self) == /\ pc[self] = "l9"
            /\ y' = 0
            /\ pc' = [pc EXCEPT ![self] = "l10"]
            /\ UNCHANGED << x, b, j, failed >>

l10(self) == /\ pc[self] = "l10"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << x, y, j, failed >>

Body(self) == \/ ncs(self) \/ start(self) \/ l1(self) \/ l2(self)
              \/ l3(self) \/ l4(self) \/ l5(self) \/ l6(self)
              \/ l7(self) \/ l8(self) \/ cs(self) \/ l9(self)
              \/ l10(self)

\* The distinguished process 1
Proc1 == Body(1)

\* The family of processes 2..N
Proc(self) == Body(self)

Next == \/ Proc1
        \/ (\E self \in 2..N : Proc(self))

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Proc1)
        /\ \A self \in 2..N : WF_vars(Proc(self))
\* END TRANSLATION

TypeOK == /\ x \in 0..N
          /\ y \in 0..N
          /\ b \in [1..N -> BOOLEAN]
          /\ j \in [ProcSet -> 1..(N+1)]
          /\ failed \in [ProcSet -> BOOLEAN]
          /\ pc \in [ProcSet -> {"ncs", "start", "l1", "l2", "l3", "l4", "l5",
                                 "l6", "l7", "l8", "cs", "l9", "l10"}]

MutualExclusion == \A i, k \in ProcSet :
                      (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

Liveness == []<>(\E i \in ProcSet : pc[i] = "cs")

THEOREM Spec => []MutualExclusion
=============================================================================