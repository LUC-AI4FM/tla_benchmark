---------------------------- MODULE Bakery ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNum

ASSUME N \in Nat \ {0}
ASSUME MaxNum \in Nat

Procs == 1..N

(***************************************************************************
--algorithm Bakery {
  variables num = [i \in Procs |-> 0], flag = [i \in Procs |-> FALSE];
  process (p \in Procs)
    variables unchecked = {}, max = 0, nxt = 1;
  {
  ncs:   while (TRUE) {
  e1:      flag[self] := TRUE;
           unchecked := Procs \ {self};
           max := 0;
  e2:      while (unchecked # {}) {
             with (i \in unchecked) {
               unchecked := unchecked \ {i};
               if (num[i] > max) { max := num[i] }
             }
           };
  e3:      num[self] := max + 1;
  e4:      flag[self] := FALSE;
           unchecked := Procs \ {self};
  wait1:   while (unchecked # {}) {
             with (i \in unchecked) { nxt := i };
             await ~ flag[nxt];
  wait2:     await \/ num[nxt] = 0
                   \/ num[self] < num[nxt]
                   \/ (num[self] = num[nxt] /\ self < nxt);
             unchecked := unchecked \ {nxt}
           };
  cs:      skip;
  exit:    num[self] := 0
         }
  }
}
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES num, flag, pc, unchecked, max, nxt

vars == << num, flag, pc, unchecked, max, nxt >>

ProcSet == Procs

Init == /\ num = [i \in Procs |-> 0]
        /\ flag = [i \in Procs |-> FALSE]
        /\ unchecked = [self \in Procs |-> {}]
        /\ max = [self \in Procs |-> 0]
        /\ nxt = [self \in Procs |-> 1]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << num, flag, unchecked, max, nxt >>

e1(self) == /\ pc[self] = "e1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
            /\ max' = [max EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED << num, nxt >>

e2(self) == /\ pc[self] = "e2"
            /\ IF unchecked[self] # {}
                  THEN /\ \E i \in unchecked[self]:
                            /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                            /\ IF num[i] > max[self]
                                  THEN max' = [max EXCEPT ![self] = num[i]]
                                  ELSE max' = max
                       /\ pc' = [pc EXCEPT ![self] = "e2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
                       /\ UNCHANGED << unchecked, max >>
            /\ UNCHANGED << num, flag, nxt >>

e3(self) == /\ pc[self] = "e3"
            /\ num' = [num EXCEPT ![self] = max[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ UNCHANGED << flag, unchecked, max, nxt >>

e4(self) == /\ pc[self] = "e4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "wait1"]
            /\ UNCHANGED << num, max, nxt >>

wait1(self) == /\ pc[self] = "wait1"
               /\ IF unchecked[self] # {}
                     THEN /\ \E i \in unchecked[self]:
                               nxt' = [nxt EXCEPT ![self] = i]
                          /\ ~ flag[nxt'[self]]
                          /\ pc' = [pc EXCEPT ![self] = "wait2"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                          /\ nxt' = nxt
               /\ UNCHANGED << num, flag, unchecked, max >>

wait2(self) == /\ pc[self] = "wait2"
               /\ \/ num[nxt[self]] = 0
                  \/ num[self] < num[nxt[self]]
                  \/ (num[self] = num[nxt[self]] /\ self < nxt[self])
               /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
               /\ pc' = [pc EXCEPT ![self] = "wait1"]
               /\ UNCHANGED << num, flag, max, nxt >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << num, flag, unchecked, max, nxt >>

exit(self) == /\ pc[self] = "exit"
              /\ num' = [num EXCEPT ![self] = 0]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED << flag, unchecked, max, nxt >>

p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
              \/ wait1(self) \/ wait2(self) \/ cs(self) \/ exit(self)

Next == \E self \in Procs : p(self)

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

-----------------------------------------------------------------------------

TypeOK == /\ num \in [Procs -> Nat]
          /\ flag \in [Procs -> BOOLEAN]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ max \in [Procs -> Nat]
          /\ nxt \in [Procs -> Procs]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4",
                               "wait1", "wait2", "cs", "exit"}]

MutualExclusion == \A i, j \in Procs : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

\* State constraint for TLC: bound ticket values
TicketConstraint == \A i \in Procs : num[i] <= MaxNum

=============================================================================