------------------------------- MODULE MCBoulanger -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N, MaxNat

ASSUME N \in Nat
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

Procs == 1 .. N

\* Lexicographic ordering on <<number, process id>> pairs
LL(a, b) == \/ a[1] < b[1]
            \/ /\ a[1] = b[1]
               /\ a[2] < b[2]

VARIABLES num, flag, unchecked, max, nxt, pc

vars == << num, flag, unchecked, max, nxt, pc >>

Init == /\ num = [i \in Procs |-> 0]
        /\ flag = [i \in Procs |-> FALSE]
        /\ unchecked = [i \in Procs |-> {}]
        /\ max = [i \in Procs |-> 0]
        /\ nxt = [i \in Procs |-> 1]
        /\ pc = [i \in Procs |-> "ncs"]

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
                           /\ max' = [max EXCEPT ![self] =
                                        IF num[i] > max[self] THEN num[i] ELSE max[self]]
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
            /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED << num, max, nxt >>

w1(self) == /\ pc[self] = "w1"
            /\ IF unchecked[self] # {}
                 THEN /\ \E i \in unchecked[self] :
                           nxt' = [nxt EXCEPT ![self] = i]
                      /\ ~ flag[nxt'[self]]
                      /\ pc' = [pc EXCEPT ![self] = "w2"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                      /\ UNCHANGED nxt
            /\ UNCHANGED << num, flag, unchecked, max >>

w2(self) == /\ pc[self] = "w2"
            /\ \/ num[nxt[self]] = 0
               \/ LL(<< num[self], self >>, << num[nxt[self]], nxt[self] >>)
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

p(self) == \/ ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
           \/ w1(self) \/ w2(self) \/ cs(self) \/ exit(self)

Next == \E self \in Procs : p(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

-----------------------------------------------------------------------------

MutualExclusion == \A i, j \in Procs : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

TypeOK == /\ num \in [Procs -> Nat]
          /\ flag \in [Procs -> BOOLEAN]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ max \in [Procs -> Nat]
          /\ nxt \in [Procs -> Procs]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4", "w1", "w2", "cs", "exit"}]

Inv == /\ TypeOK
       /\ MutualExclusion
       /\ \A i \in Procs :
             /\ (pc[i] \in {"e4", "w1", "w2", "cs"}) => (num[i] # 0)
             /\ (pc[i] \in {"e2", "e3"}) => flag[i]
             /\ (pc[i] \in {"ncs", "e1", "e2", "e3"}) => (num[i] = 0 \/ pc[i] # "ncs" \/ num[i] = 0)

StateConstraint == \A process \in Procs : num[process] < MaxNat

=============================================================================