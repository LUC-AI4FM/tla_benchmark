--------------------------- MODULE FastMutex ---------------------------
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 1

(***************************************************************************
--algorithm FastMutex {
  variables x = 0, y = 0, b = [i \in 1..N |-> FALSE],
            failed = [i \in 1..N |-> FALSE];

  process (P1 = 1)
    variable j = 1;
  {
    ncs:  while (TRUE) {
            skip;
    start:  b[self] := TRUE;
    l1:     x := self;
    l2:     if (y # 0) {
    l3:       b[self] := FALSE;
    l4:       await y = 0;
              goto start };
    l5:     y := self;
    l6:     if (x # self) {
    l7:       b[self] := FALSE;
              j := 1;
    l8:       while (j <= N) { await ~b[j]; j := j + 1 };
    l9:       if (y # self) {
    l10:        await y = 0;
                goto start } };
    cs:     skip;
    l11:    y := 0;
    l12:    b[self] := FALSE }
  }

  process (P \in 2..N)
    variable j = 1;
  {
    ncs:  while (TRUE) {
            either skip
            or { failed[self] := TRUE; goto Done };
    start:  b[self] := TRUE;
    ... (same as P1) ...
  }
}
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES x, y, b, failed, pc, j

vars == << x, y, b, failed, pc, j >>

ProcSet == {1} \cup (2..N)

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ failed = [i \in 1..N |-> FALSE]
        /\ j = [self \in ProcSet |-> 1]
        /\ pc = [self \in ProcSet |-> "ncs"]

Goto(self, l) == pc' = [pc EXCEPT ![self] = l]

ncs1(self) == /\ pc[self] = "ncs"
              /\ Goto(self, "start")
              /\ UNCHANGED << x, y, b, failed, j >>

ncs2(self) == /\ pc[self] = "ncs"
              /\ \/ /\ Goto(self, "start")
                    /\ UNCHANGED failed
                 \/ /\ failed' = [failed EXCEPT ![self] = TRUE]
                    /\ Goto(self, "Done")
              /\ UNCHANGED << x, y, b, j >>

start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ Goto(self, "l1")
               /\ UNCHANGED << x, y, failed, j >>

l1(self) == /\ pc[self] = "l1"
            /\ x' = self
            /\ Goto(self, "l2")
            /\ UNCHANGED << y, b, failed, j >>

l2(self) == /\ pc[self] = "l2"
            /\ IF y # 0 THEN Goto(self, "l3") ELSE Goto(self, "l5")
            /\ UNCHANGED << x, y, b, failed, j >>

l3(self) == /\ pc[self] = "l3"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ Goto(self, "l4")
            /\ UNCHANGED << x, y, failed, j >>

l4(self) == /\ pc[self] = "l4"
            /\ y = 0
            /\ Goto(self, "start")
            /\ UNCHANGED << x, y, b, failed, j >>

l5(self) == /\ pc[self] = "l5"
            /\ y' = self
            /\ Goto(self, "l6")
            /\ UNCHANGED << x, b, failed, j >>

l6(self) == /\ pc[self] = "l6"
            /\ IF x # self THEN Goto(self, "l7") ELSE Goto(self, "cs")
            /\ UNCHANGED << x, y, b, failed, j >>

l7(self) == /\ pc[self] = "l7"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ Goto(self, "l8")
            /\ UNCHANGED << x, y, failed >>

l8(self) == /\ pc[self] = "l8"
            /\ IF j[self] <= N
                  THEN /\ ~b[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ Goto(self, "l8")
                  ELSE /\ Goto(self, "l9")
                       /\ UNCHANGED j
            /\ UNCHANGED << x, y, b, failed >>

l9(self) == /\ pc[self] = "l9"
            /\ IF y # self THEN Goto(self, "l10") ELSE Goto(self, "cs")
            /\ UNCHANGED << x, y, b, failed, j >>

l10(self) == /\ pc[self] = "l10"
             /\ y = 0
             /\ Goto(self, "start")
             /\ UNCHANGED << x, y, b, failed, j >>

cs(self) == /\ pc[self] = "cs"
            /\ Goto(self, "l11")
            /\ UNCHANGED << x, y, b, failed, j >>

l11(self) == /\ pc[self] = "l11"
             /\ y' = 0
             /\ Goto(self, "l12")
             /\ UNCHANGED << x, b, failed, j >>

l12(self) == /\ pc[self] = "l12"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ Goto(self, "ncs")
             /\ UNCHANGED << x, y, failed, j >>

Body(self) == \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self)
              \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self)
              \/ l8(self) \/ l9(self) \/ l10(self) \/ cs(self)
              \/ l11(self) \/ l12(self)

P1(self) == ncs1(self) \/ Body(self)

P(self) == ncs2(self) \/ Body(self)

Next == \/ P1(1)
        \/ (\E self \in 2..N : P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(P1(1))
        /\ \A self \in 2..N : WF_vars(P(self))
\* END TRANSLATION

TypeOK == /\ x \in 0..N
          /\ y \in 0..N
          /\ b \in [1..N -> BOOLEAN]
          /\ failed \in [1..N -> BOOLEAN]
          /\ j \in [ProcSet -> 1..(N+1)]

MutualExclusion ==
  \A p, q \in ProcSet : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

Liveness == []<>(\E p \in ProcSet : pc[p] = "cs")

THEOREM Spec => []MutualExclusion
THEOREM Spec => Liveness
=============================================================================