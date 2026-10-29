---------------------------- MODULE OneBitMutex ----------------------------
EXTENDS Integers, Naturals, TLC

CONSTANT N

ASSUME NAssump == N \in Nat /\ N > 0

Procs == 1..N

(***************************************************************************
--algorithm OneBitMutex {
  variable flag = [i \in Procs |-> FALSE] ;
  process (P \in Procs)
    variable j = 1 ;
  {
    ncs: while (TRUE) {
           skip ;   \* noncritical section
    e1:    flag[self] := TRUE ;
           j := 1 ;
    e2:    while (j < self) {
             if (flag[j]) {
    e3:        flag[self] := FALSE ;
    e4:        await ~flag[j] ;
               goto e1
             } else { j := j + 1 }
           } ;
    e5:    j := self + 1 ;
    e6:    while (j <= N) {
             await ~flag[j] ;
             j := j + 1
           } ;
    cs:    skip ;   \* critical section
    f:     flag[self] := FALSE
         }
  }
}
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES flag, pc, j

vars == << flag, pc, j >>

ProcSet == Procs

Init == /\ flag = [i \in Procs |-> FALSE]
        /\ j = [self \in Procs |-> 1]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << flag, j >>

e1(self) == /\ pc[self] = "e1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "e2"]

e2(self) == /\ pc[self] = "e2"
            /\ IF j[self] < self
                  THEN /\ IF flag[j[self]]
                             THEN /\ pc' = [pc EXCEPT ![self] = "e3"]
                                  /\ j' = j
                             ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
                                  /\ pc' = [pc EXCEPT ![self] = "e2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e5"]
                       /\ j' = j
            /\ flag' = flag

e3(self) == /\ pc[self] = "e3"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ j' = j

e4(self) == /\ pc[self] = "e4"
            /\ ~flag[j[self]]
            /\ pc' = [pc EXCEPT ![self] = "e1"]
            /\ UNCHANGED << flag, j >>

e5(self) == /\ pc[self] = "e5"
            /\ j' = [j EXCEPT ![self] = self + 1]
            /\ pc' = [pc EXCEPT ![self] = "e6"]
            /\ flag' = flag

e6(self) == /\ pc[self] = "e6"
            /\ IF j[self] <= N
                  THEN /\ ~flag[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "e6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ j' = j
            /\ flag' = flag

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "f"]
            /\ UNCHANGED << flag, j >>

f(self) == /\ pc[self] = "f"
           /\ flag' = [flag EXCEPT ![self] = FALSE]
           /\ pc' = [pc EXCEPT ![self] = "ncs"]
           /\ j' = j

P(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
              \/ e5(self) \/ e6(self) \/ cs(self) \/ f(self)

Next == (\E self \in Procs : P(self))

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK == /\ flag \in [Procs -> BOOLEAN]
          /\ j \in [Procs -> 1..(N+1)]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4",
                               "e5", "e6", "cs", "f"}]

MutualExclusion == \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

=============================================================================