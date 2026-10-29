---------------------------- MODULE MCBoulanger ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

ASSUME NAssump == N \in Nat \ {0}
ASSUME MaxNatAssump == MaxNat \in Nat

Procs == 1 .. N

NatOverride == 0 .. MaxNat

\* Lexicographic ordering on <<ticket, process id>> pairs
LL(a, b) == \/ a[1] < b[1]
            \/ (a[1] = b[1] /\ a[2] < b[2])

VARIABLES num, flag, unchecked, max, nxt, pc

vars == << num, flag, unchecked, max, nxt, pc >>

Labels == {"ncs", "e1", "e2", "e3", "e4", "w1", "w2", "cs", "exit"}

TypeOK ==
    /\ num \in [Procs -> NatOverride]
    /\ flag \in [Procs -> BOOLEAN]
    /\ unchecked \in [Procs -> SUBSET Procs]
    /\ max \in [Procs -> NatOverride]
    /\ nxt \in [Procs -> Procs]
    /\ pc \in [Procs -> Labels]

Init ==
    /\ num = [i \in Procs |-> 0]
    /\ flag = [i \in Procs |-> FALSE]
    /\ unchecked = [i \in Procs |-> {}]
    /\ max = [i \in Procs |-> 0]
    /\ nxt = [i \in Procs |-> CHOOSE j \in Procs : TRUE]
    /\ pc = [i \in Procs |-> "ncs"]

ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << num, flag, unchecked, max, nxt >>

e1(self) ==
    /\ pc[self] = "e1"
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
    /\ max' = [max EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED << num, nxt >>

e2(self) ==
    /\ pc[self] = "e2"
    /\ IF unchecked[self] # {}
         THEN \E i \in unchecked[self] :
                /\ nxt' = [nxt EXCEPT ![self] = i]
                /\ unchecked' = [unchecked EXCEPT ![self] = @ \ {i}]
                /\ max' = [max EXCEPT ![self] =
                             IF num[i] > max[self] THEN num[i] ELSE max[self]]
                /\ pc' = [pc EXCEPT ![self] = "e2"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
              /\ UNCHANGED << unchecked, max, nxt >>
    /\ UNCHANGED << num, flag >>

e3(self) ==
    /\ pc[self] = "e3"
    /\ \E k \in {j \in NatOverride : j > max[self]} :
          num' = [num EXCEPT ![self] = k]
    /\ pc' = [pc EXCEPT ![self] = "e4"]
    /\ UNCHANGED << flag, unchecked, max, nxt >>

e4(self) ==
    /\ pc[self] = "e4"
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
    /\ pc' = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED << num, max, nxt >>

w1(self) ==
    /\ pc[self] = "w1"
    /\ IF unchecked[self] # {}
         THEN \E i \in unchecked[self] :
                /\ ~ flag[i]
                /\ nxt' = [nxt EXCEPT ![self] = i]
                /\ pc' = [pc EXCEPT ![self] = "w2"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED nxt
    /\ UNCHANGED << num, flag, unchecked, max >>

w2(self) ==
    /\ pc[self] = "w2"
    /\ \/ num[nxt[self]] = 0
       \/ LL(<< num[self], self >>, << num[nxt[self]], nxt[self] >>)
    /\ unchecked' = [unchecked EXCEPT ![self] = @ \ {nxt[self]}]
    /\ pc' = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED << num, flag, max, nxt >>

cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED << num, flag, unchecked, max, nxt >>

exit(self) ==
    /\ pc[self] = "exit"
    /\ num' = [num EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << flag, unchecked, max, nxt >>

pNoNcs(self) ==
    \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
    \/ w1(self) \/ w2(self) \/ cs(self) \/ exit(self)

p(self) == ncs(self) \/ pNoNcs(self)

Next == \E self \in Procs : p(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(pNoNcs(self))

-----------------------------------------------------------------------------
\* Bounding state constraint contributed by this wrapper
StateConstraint == \A process \in Procs : num[process] < MaxNat

\* Safety
MutualExclusion == \A i, j \in Procs : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

\* Liveness
StarvationFree == \A i \in Procs : (pc[i] = "e1") ~> (pc[i] = "cs")

DeadlockFree == (\E i \in Procs : pc[i] = "e1") ~> (\E i \in Procs : pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
=============================================================================