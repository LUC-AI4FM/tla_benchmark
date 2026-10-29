------------------------------ MODULE Bakery ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS NumProcs, MaxNum

ASSUME NumProcs \in Nat /\ NumProcs >= 1
ASSUME MaxNum \in Nat

Procs == 1..NumProcs

\* Lexicographic ordering on <<ticket, pid>> pairs
LL(a, b) == \/ a[1] < b[1]
            \/ /\ a[1] = b[1]
               /\ a[2] < b[2]

VARIABLES num, flag, pc, unchecked, max, nxt

vars == <<num, flag, pc, unchecked, max, nxt>>

Init == /\ num = [i \in Procs |-> 0]
        /\ flag = [i \in Procs |-> FALSE]
        /\ unchecked = [i \in Procs |-> {}]
        /\ max = [i \in Procs |-> 0]
        /\ nxt = [i \in Procs |-> 1]
        /\ pc = [i \in Procs |-> "ncs"]

\* Non-critical section: decide to try to enter
ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED <<num, flag, unchecked, max, nxt>>

\* Begin choosing: raise flag, prepare to scan the others
e1(self) == /\ pc[self] = "e1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
            /\ max' = [max EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED <<num, nxt>>

\* Read other processes' tickets one at a time, nondeterministic order
e2(self) == /\ pc[self] = "e2"
            /\ IF unchecked[self] # {}
                 THEN \E i \in unchecked[self] :
                        /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                        /\ IF num[i] > max[self]
                             THEN max' = [max EXCEPT ![self] = num[i]]
                             ELSE max' = max
                        /\ pc' = [pc EXCEPT ![self] = "e2"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
                      /\ UNCHANGED <<unchecked, max>>
            /\ UNCHANGED <<num, flag, nxt>>

\* Take a ticket one higher than the maximum observed
e3(self) == /\ pc[self] = "e3"
            /\ num' = [num EXCEPT ![self] = max[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ UNCHANGED <<flag, unchecked, max, nxt>>

\* Done choosing: lower flag, prepare to wait on the others
e4(self) == /\ pc[self] = "e4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED <<num, max, nxt>>

\* Pick another process to check; wait until it is not choosing
w1(self) == /\ pc[self] = "w1"
            /\ IF unchecked[self] # {}
                 THEN \E i \in unchecked[self] :
                        /\ nxt' = [nxt EXCEPT ![self] = i]
                        /\ ~ flag[i]
                        /\ pc' = [pc EXCEPT ![self] = "w2"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                      /\ nxt' = nxt
            /\ UNCHANGED <<num, flag, unchecked, max>>

\* Wait until the chosen process is not ahead of us
w2(self) == /\ pc[self] = "w2"
            /\ \/ num[nxt[self]] = 0
               \/ LL(<<num[self], self>>, <<num[nxt[self]], nxt[self]>>)
            /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
            /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED <<num, flag, max, nxt>>

\* Critical section
cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED <<num, flag, unchecked, max, nxt>>

\* Exit: reset ticket and repeat
exit(self) == /\ pc[self] = "exit"
              /\ num' = [num EXCEPT ![self] = 0]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED <<flag, unchecked, max, nxt>>

p(self) == \/ ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
           \/ w1(self) \/ w2(self) \/ cs(self) \/ exit(self)

Next == \E self \in Procs : p(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

-----------------------------------------------------------------------------

TypeOK == /\ num \in [Procs -> Nat]
          /\ flag \in [Procs -> BOOLEAN]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ max \in [Procs -> Nat]
          /\ nxt \in [Procs -> Procs]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4", "w1", "w2", "cs", "exit"}]

MutualExclusion == \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Invariant == TypeOK /\ MutualExclusion

Constraint == \A i \in Procs : num[i] <= MaxNum

=============================================================================