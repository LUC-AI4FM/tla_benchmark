---------------------------- MODULE Bakery ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS NumProcs, MaxNum

ASSUME NumProcs \in Nat /\ MaxNum \in Nat

Procs == 1..NumProcs

LexLess(a, b) == \/ a[1] < b[1]
                 \/ (a[1] = b[1] /\ a[2] < b[2])

(***************************************************************************
--algorithm Bakery {
  variables num = [i \in Procs |-> 0], flag = [i \in Procs |-> FALSE];
  process (p \in Procs)
    variables unchecked = {}, max = 0, nxt = 1;
  {
  ncs: while (TRUE) {
         skip;
  e1:    flag[self] := TRUE;
         unchecked := Procs \ {self};
         max := 0;
  e2:    while (unchecked # {}) {
           with (i \in unchecked) {
             unchecked := unchecked \ {i};
             if (num[i] > max) { max := num[i] }
           }
         };
  e3:    num[self] := max + 1;
  e4:    flag[self] := FALSE;
         unchecked := Procs \ {self};
  w1:    while (unchecked # {}) {
           with (i \in unchecked) { nxt := i };
  w2:      await ~flag[nxt];
  w3:      await \/ num[nxt] = 0
                 \/ LexLess(<<num[self], self>>, <<num[nxt], nxt>>);
           unchecked := unchecked \ {nxt}
         };
  cs:    skip;
  exit:  num[self] := 0
       }
  }
}
***************************************************************************)

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
                 THEN /\ \E i \in unchecked[self] :
                           /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                           /\ IF num[i] > max[self]
                                THEN max' = [max EXCEPT ![self] = num[i]]
                                ELSE max' = max
                      /\ pc' = [pc EXCEPT ![self] = "e2"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
                      /\ UNCHANGED << unchecked, max >>
            /\ UNCHANGED << num, flag, nxt >>

ChooseNumber(self) == /\ pc[self] = "e3"
                      /\ num' = [num EXCEPT ![self] = max[self] + 1]
                      /\ pc' = [pc EXCEPT ![self] = "e4"]
                      /\ UNCHANGED << flag, unchecked, max, nxt >>

e3(self) == ChooseNumber(self)

e4(self) == /\ pc[self] = "e4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED << num, max, nxt >>

w1(self) == /\ pc[self] = "w1"
            /\ IF unchecked[self] # {}
                 THEN /\ \E i \in unchecked[self] :
                           nxt' = [nxt EXCEPT ![self] = i]
                      /\ pc' = [pc EXCEPT ![self] = "w2"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                      /\ nxt' = nxt
            /\ UNCHANGED << num, flag, unchecked, max >>

w2(self) == /\ pc[self] = "w2"
            /\ ~flag[nxt[self]]
            /\ pc' = [pc EXCEPT ![self] = "w3"]
            /\ UNCHANGED << num, flag, unchecked, max, nxt >>

w3(self) == /\ pc[self] = "w3"
            /\ \/ num[nxt[self]] = 0
               \/ LexLess(<<num[self], self>>, <<num[nxt[self]], nxt[self]>>)
            /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
            /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED << num, flag, max, nxt >>

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << num, flag, unchecked, max, nxt >>

exit(self) == /\ pc[self] = "exit"
              /\ num' = [num EXCEPT ![self] = 0]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED << flag, unchecked, max, nxt >>

p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
           \/ w1(self) \/ w2(self) \/ w3(self) \/ cs(self) \/ exit(self)

Next == \E self \in Procs : p(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

-----------------------------------------------------------------------------

InCS(i) == pc[i] = "cs"

TypeOK == /\ num \in [Procs -> Nat]
          /\ flag \in [Procs -> BOOLEAN]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ max \in [Procs -> Nat]
          /\ nxt \in [Procs -> Procs]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4",
                               "w1", "w2", "w3", "cs", "exit"}]

MutualExclusion == \A i, j \in Procs : (i # j) => ~(InCS(i) /\ InCS(j))

Invariant == TypeOK /\ MutualExclusion

Constraint == \A i \in Procs : num[i] <= MaxNum

CSCount == Cardinality({i \in Procs : InCS(i)})

PossibleCounts == 0..1

_POSSIBLE == CSCount \in PossibleCounts

=============================================================================