--------------------------- MODULE FastMutex ---------------------------
EXTENDS Naturals, TLC

CONSTANT N, defaultInitValue

ASSUME N \in Nat

ASSUME TLCSet(1, 0) /\ TLCSet(2, 0)

(***************************************************************************
--algorithm Fast {
  variables x = defaultInitValue, y = 0, b = [i \in 1..N |-> FALSE];
  process (Proc \in 1..N)
    variables j = defaultInitValue, failed = FALSE;
  {
    ncs: while (TRUE) {
           skip;  \* noncritical section
    start: b[self] := TRUE;
    l1:    x := self;
    l2:    if (y # 0) { l3: b[self] := FALSE;
                        l4: await y = 0;
                            goto start };
    l5:    y := self;
    l6:    if (x # self) { l7: b[self] := FALSE;
                               j := 1;
                           l8: while (j <= N) { await ~b[j];
                                                j := j + 1 };
                           l9: if (y # self) { l10: await y = 0;
                                                    failed := TRUE } };
    cs:    if (~failed) { skip;  \* critical section
                          l11: y := 0;
                          l12: b[self] := FALSE }
           else { failed := FALSE }
         }
  }
}
 ***************************************************************************)

VARIABLES x, y, b, pc, j, failed

vars == << x, y, b, pc, j, failed >>

ProcSet == (1..N)

Init == /\ x = defaultInitValue
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ j = [self \in ProcSet |-> defaultInitValue]
        /\ failed = [self \in ProcSet |-> FALSE]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j, failed >>

start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "l1"]
               /\ UNCHANGED << x, y, j, failed >>

l1(self) == /\ pc[self] = "l1"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << y, b, j, failed >>

l2(self) == /\ pc[self] = "l2"
            /\ IF y # 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "l3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << x, y, b, j, failed >>

l3(self) == /\ pc[self] = "l3"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ UNCHANGED << x, y, j, failed >>

l4(self) == /\ pc[self] = "l4"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j, failed >>

l5(self) == /\ pc[self] = "l5"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "l6"]
            /\ UNCHANGED << x, b, j, failed >>

l6(self) == /\ pc[self] = "l6"
            /\ IF x # self
                  THEN /\ pc' = [pc EXCEPT ![self] = "l7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j, failed >>

l7(self) == /\ pc[self] = "l7"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l8"]
            /\ UNCHANGED << x, y, failed >>

l8(self) == /\ pc[self] = "l8"
            /\ IF j[self] <= N
                  THEN /\ ~b[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "l8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l9"]
                       /\ j' = j
            /\ UNCHANGED << x, y, b, failed >>

l9(self) == /\ pc[self] = "l9"
            /\ IF y # self
                  THEN /\ pc' = [pc EXCEPT ![self] = "l10"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j, failed >>

l10(self) == /\ pc[self] = "l10"
             /\ y = 0
             /\ failed' = [failed EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << x, y, b, j >>

cs(self) == /\ pc[self] = "cs"
            /\ IF ~failed[self]
                  THEN /\ TRUE
                       /\ pc' = [pc EXCEPT ![self] = "l11"]
                       /\ failed' = failed
                  ELSE /\ failed' = [failed EXCEPT ![self] = FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "ncs"]
            /\ UNCHANGED << x, y, b, j >>

l11(self) == /\ pc[self] = "l11"
             /\ y' = 0
             /\ pc' = [pc EXCEPT ![self] = "l12"]
             /\ UNCHANGED << x, b, j, failed >>

l12(self) == /\ pc[self] = "l12"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << x, y, j, failed >>

Proc(self) == ncs(self) \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self)
                \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self)
                \/ l9(self) \/ l10(self) \/ cs(self) \/ l11(self)
                \/ l12(self)

Next == (\E self \in 1..N: Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(Proc(self))

-----------------------------------------------------------------------------

InCS(p) == pc[p] = "cs" /\ ~failed[p]

Invariant == \A p, q \in 1..N : (p # q) => ~(InCS(p) /\ InCS(q))

SomeoneInCS == \E p \in 1..N : pc[p] = "cs"

Liveness == []<>SomeoneInCS

Contention == \E p, q \in 1..N : /\ p # q
                                /\ pc[p] \in {"l5", "l6"}
                                /\ pc[q] \in {"l5", "l6"}

_POSSIBLE == /\ (SomeoneInCS => TLCSet(1, TLCGet(1) + 1))
             /\ (Contention  => TLCSet(2, TLCGet(2) + 1))

PossibleCounts == /\ TLCGet(1) = 292
                  /\ TLCGet(2) = 16

=============================================================================