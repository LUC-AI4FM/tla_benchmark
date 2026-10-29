------------------------------- MODULE Bakery -------------------------------
EXTENDS Naturals, TLC

CONSTANTS NumProcs, MaxNum

Proc == 1..NumProcs

VARIABLES num, choosing, read, max, nxt, pc

vars == << num, choosing, read, max, nxt, pc >>

Init ==
    /\ num = [i \in Proc |-> 0]
    /\ choosing = [i \in Proc |-> FALSE]
    /\ read = [i \in Proc |-> {}]
    /\ max = [i \in Proc |-> 0]
    /\ nxt = [i \in Proc |-> 1]
    /\ pc = [i \in Proc |-> "loop"]

loop(self) ==
    /\ pc[self] = "loop"
    /\ choosing' = [choosing EXCEPT ![self] = TRUE]
    /\ read' = [read EXCEPT ![self] = Proc \ {self}]
    /\ max' = [max EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "d1"]
    /\ UNCHANGED << num, nxt >>

d1(self) ==
    /\ pc[self] = "d1"
    /\ IF read[self] # {}
         THEN \E j \in read[self] :
                /\ max' = [max EXCEPT ![self] =
                             IF num[j] > max[self] THEN num[j] ELSE max[self]]
                /\ read' = [read EXCEPT ![self] = read[self] \ {j}]
                /\ pc' = [pc EXCEPT ![self] = "d1"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "d2"]
              /\ UNCHANGED << read, max >>
    /\ UNCHANGED << num, choosing, nxt >>

d2(self) ==
    /\ pc[self] = "d2"
    /\ num' = [num EXCEPT ![self] = max[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "d3"]
    /\ UNCHANGED << choosing, read, max, nxt >>

d3(self) ==
    /\ pc[self] = "d3"
    /\ choosing' = [choosing EXCEPT ![self] = FALSE]
    /\ read' = [read EXCEPT ![self] = Proc \ {self}]
    /\ pc' = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED << num, max, nxt >>

w1(self) ==
    /\ pc[self] = "w1"
    /\ IF read[self] # {}
         THEN \E j \in read[self] :
                /\ ~choosing[j]
                /\ nxt' = [nxt EXCEPT ![self] = j]
                /\ pc' = [pc EXCEPT ![self] = "w2"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED nxt
    /\ UNCHANGED << num, choosing, read, max >>

w2(self) ==
    /\ pc[self] = "w2"
    /\ LET j == nxt[self] IN
         \/ num[j] = 0
         \/ num[j] > num[self]
         \/ (num[j] = num[self] /\ self < j)
    /\ read' = [read EXCEPT ![self] = read[self] \ {nxt[self]}]
    /\ pc' = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED << num, choosing, max, nxt >>

cs(self) ==
    /\ pc[self] = "cs"
    /\ num' = [num EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "loop"]
    /\ UNCHANGED << choosing, read, max, nxt >>

p(self) ==
    \/ loop(self) \/ d1(self) \/ d2(self) \/ d3(self)
    \/ w1(self) \/ w2(self) \/ cs(self)

Next == \E self \in Proc : p(self)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

Invariant == \A i, j \in Proc : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Constraint == \A i \in Proc : num[i] <= MaxNum

InCS == \E i \in Proc : pc[i] = "cs"

ChooseNumber == \E i \in Proc : pc[i] \in {"d1", "d2", "d3"}

ASSUME TLCSet(1, 0) /\ TLCSet(2, 0)

_POSSIBLE ==
    /\ IF InCS THEN TLCSet(1, TLCGet(1) + 1) ELSE TRUE
    /\ IF ChooseNumber THEN TLCSet(2, TLCGet(2) + 1) ELSE TRUE

PossibleCounts ==
    /\ TLCGet(1) = 113
    /\ TLCGet(2) = 180

=============================================================================