---------------------------- MODULE CBakery ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS NumProcs, MaxNum

ASSUME NumProcs \in Nat \ {0}
ASSUME MaxNum \in Nat

Procs == 1..NumProcs

VARIABLES num, choosing, read, max, nxt, pc

vars == << num, choosing, read, max, nxt, pc >>

ProcSet == Procs

Init ==
    /\ num = [i \in Procs |-> 0]
    /\ choosing = [i \in Procs |-> FALSE]
    /\ read = [self \in ProcSet |-> {}]
    /\ max = [self \in ProcSet |-> 0]
    /\ nxt = [self \in ProcSet |-> 1]
    /\ pc = [self \in ProcSet |-> "d1"]

d1(self) ==
    /\ pc[self] = "d1"
    /\ choosing' = [choosing EXCEPT ![self] = TRUE]
    /\ read' = [read EXCEPT ![self] = {self}]
    /\ max' = [max EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "d2"]
    /\ UNCHANGED << num, nxt >>

d2(self) ==
    /\ pc[self] = "d2"
    /\ IF read[self] # Procs
         THEN /\ \E p \in Procs \ read[self] :
                   /\ IF num[p] > max[self]
                        THEN max' = [max EXCEPT ![self] = num[p]]
                        ELSE max' = max
                   /\ read' = [read EXCEPT ![self] = read[self] \cup {p}]
              /\ pc' = [pc EXCEPT ![self] = "d2"]
              /\ num' = num
         ELSE /\ num' = [num EXCEPT ![self] = max[self] + 1]
              /\ pc' = [pc EXCEPT ![self] = "d3"]
              /\ UNCHANGED << max, read >>
    /\ UNCHANGED << choosing, nxt >>

d3(self) ==
    /\ pc[self] = "d3"
    /\ choosing' = [choosing EXCEPT ![self] = FALSE]
    /\ read' = [read EXCEPT ![self] = {self}]
    /\ pc' = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED << num, max, nxt >>

w1(self) ==
    /\ pc[self] = "w1"
    /\ IF read[self] # Procs
         THEN /\ \E p \in Procs \ read[self] :
                   nxt' = [nxt EXCEPT ![self] = p]
              /\ ~choosing[nxt'[self]]
              /\ pc' = [pc EXCEPT ![self] = "w2"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ nxt' = nxt
    /\ UNCHANGED << num, choosing, read, max >>

w2(self) ==
    /\ pc[self] = "w2"
    /\ \/ num[nxt[self]] = 0
       \/ num[nxt[self]] > num[self]
       \/ /\ num[nxt[self]] = num[self]
          /\ self < nxt[self]
    /\ read' = [read EXCEPT ![self] = read[self] \cup {nxt[self]}]
    /\ pc' = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED << num, choosing, max, nxt >>

cs(self) ==
    /\ pc[self] = "cs"
    /\ num' = [num EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "d1"]
    /\ UNCHANGED << choosing, read, max, nxt >>

p(self) == d1(self) \/ d2(self) \/ d3(self) \/ w1(self) \/ w2(self) \/ cs(self)

Next == \E self \in Procs : p(self)

Spec == Init /\ [][Next]_vars

\* State constraint for model checking: bound ticket numbers
Constraint == \A i \in Procs : num[i] <= MaxNum

\* Type invariant
TypeOK ==
    /\ num \in [Procs -> Nat]
    /\ choosing \in [Procs -> BOOLEAN]
    /\ read \in [Procs -> SUBSET Procs]
    /\ max \in [Procs -> Nat]
    /\ nxt \in [Procs -> Procs]
    /\ pc \in [Procs -> {"d1", "d2", "d3", "w1", "w2", "cs"}]

\* Mutual exclusion invariant
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

=============================================================================