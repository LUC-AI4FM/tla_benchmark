------------------------------ MODULE OneBitMutex ------------------------------
EXTENDS Integers, Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 1

Procs == 1..N

(***************************************************************************
--algorithm OneBitMutex {
  variable x = [i \in Procs |-> FALSE];
  process (p \in Procs)
    variable j = 1;
  {
    ncs: while (TRUE) {
           skip;
    e1:    x[self] := TRUE;
           j := 1;
    e2:    while (j < self) {
             if (x[j]) {
    e3:        x[self] := FALSE;
    e4:        await ~x[j];
               goto e1
             } else {
               j := j + 1
             }
           };
           j := self + 1;
    e6:    while (j <= N) {
             await ~x[j];
             j := j + 1
           };
    cs:    skip;
    f:     x[self] := FALSE
         }
  }
}
***************************************************************************)

VARIABLES x, pc, j

vars == << x, pc, j >>

ProcSet == Procs

Init == /\ x = [i \in Procs |-> FALSE]
        /\ j = [self \in Procs |-> 1]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << x, j >>

e1(self) == /\ pc[self] = "e1"
            /\ x' = [x EXCEPT ![self] = TRUE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "e2"]

e2(self) == /\ pc[self] = "e2"
            /\ IF j[self] < self
                  THEN IF x[j[self]]
                          THEN /\ pc' = [pc EXCEPT ![self] = "e3"]
                               /\ j' = j
                          ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
                               /\ pc' = [pc EXCEPT ![self] = "e2"]
                  ELSE /\ j' = [j EXCEPT ![self] = self + 1]
                       /\ pc' = [pc EXCEPT ![self] = "e6"]
            /\ x' = x

e3(self) == /\ pc[self] = "e3"
            /\ x' = [x EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ j' = j

e4(self) == /\ pc[self] = "e4"
            /\ ~x[j[self]]
            /\ pc' = [pc EXCEPT ![self] = "e1"]
            /\ UNCHANGED << x, j >>

e6(self) == /\ pc[self] = "e6"
            /\ IF j[self] <= N
                  THEN /\ ~x[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "e6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ j' = j
            /\ x' = x

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "f"]
            /\ UNCHANGED << x, j >>

f(self) == /\ pc[self] = "f"
           /\ x' = [x EXCEPT ![self] = FALSE]
           /\ pc' = [pc EXCEPT ![self] = "ncs"]
           /\ j' = j

p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
              \/ e6(self) \/ cs(self) \/ f(self)

Next == \E self \in Procs : p(self)

Spec == Init /\ [][Next]_vars

TypeOK == /\ x \in [Procs -> BOOLEAN]
          /\ j \in [Procs -> 1..(N+1)]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4", "e6", "cs", "f"}]

MutualExclusion == \A a, b \in Procs : (a # b) => ~(pc[a] = "cs" /\ pc[b] = "cs")

=============================================================================