---- MODULE CBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS NumProcs, MaxNum

ASSUME NumProcs \in Nat /\ MaxNum \in Nat

ProcSet == 1..NumProcs

VARIABLES num, choosing, read, max, nxt, pc

vars == << num, choosing, read, max, nxt, pc >>

Init ==
    /\ num = [i \in ProcSet |-> 0]
    /\ choosing = [i \in ProcSet |-> FALSE]
    /\ read = [i \in ProcSet |-> {}]
    /\ max = [i \in ProcSet |-> 0]
    /\ nxt = [i \in ProcSet |-> 1]
    /\ pc = [i \in ProcSet |-> "d1"]

d1(self) ==
    /\ pc[self] = "d1"
    /\ choosing' = [choosing EXCEPT ![self] = TRUE]
    /\ read' = [read EXCEPT ![self] = {self}]
    /\ max' = [max EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "d2"]
    /\ UNCHANGED << num, nxt >>

d2(self) ==
    /\ pc[self] = "d2"
    /\ IF read[self] # ProcSet
         THEN /\ \E p \in ProcSet \ read[self] :
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
    /\ IF read[self] # ProcSet
         THEN /\ \E p \in ProcSet \ read[self] :
                   /\ ~choosing[p]
                   /\ nxt' = [nxt EXCEPT ![self] = p]
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
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED << num, choosing, read, max, nxt >>

exit(self) ==
    /\ pc[self] = "exit"
    /\ num' = [num EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "d1"]
    /\ UNCHANGED << choosing, read, max, nxt >>

P(self) == d1(self) \/ d2(self) \/ d3(self) \/ w1(self) \/ w2(self)
           \/ cs(self) \/ exit(self)

Next == \E self \in ProcSet : P(self)

Spec == Init /\ [][Next]_vars

Invariant == \A i, j \in ProcSet : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Constraint == \A i \in ProcSet : num[i] <= MaxNum

====