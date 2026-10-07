---- MODULE CBakery ----
EXTENDS Naturals, TLC

CONSTANTS NumProcs, MaxNum

VARIABLES pc, num, choosing, read, max, nxt

Proc == 1..NumProcs

MMax(m, n) == IF m >= n THEN m ELSE n

Init ==
  /\ pc = [i \in Proc |-> "d1"]
  /\ num = [i \in Proc |-> 0]
  /\ choosing = [i \in Proc |-> FALSE]
  /\ read = [i \in Proc |-> 1]
  /\ max = [i \in Proc |-> 0]
  /\ nxt = [i \in Proc |-> 0]

d1(i) ==
  /\ pc[i] = "d1"
  /\ pc' = [pc EXCEPT ![i] = "d2"]
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ read' = [read EXCEPT ![i] = 1]
  /\ max' = [max EXCEPT ![i] = 0]
  /\ UNCHANGED << num, nxt >>

d2scan(i) ==
  /\ pc[i] = "d2"
  /\ read[i] <= NumProcs
  /\ LET j == read[i] IN
     /\ max' = [max EXCEPT ![i] = IF j # i THEN MMax(max[i], num[j]) ELSE max[i]]
     /\ read' = [read EXCEPT ![i] = j + 1]
     /\ pc' = [pc EXCEPT ![i] = "d2"]
     /\ UNCHANGED << num, choosing, nxt >>

d2done(i) ==
  /\ pc[i] = "d2"
  /\ read[i] > NumProcs
  /\ nxt' = [nxt EXCEPT ![i] = max[i] + 1]
  /\ pc' = [pc EXCEPT ![i] = "d3"]
  /\ UNCHANGED << num, choosing, read, max >>

d3(i) ==
  /\ pc[i] = "d3"
  /\ num' = [num EXCEPT ![i] = nxt[i]]
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "w1"]
  /\ UNCHANGED << read, max, nxt >>

w1(i) ==
  /\ pc[i] = "w1"
  /\ read' = [read EXCEPT ![i] = 1]
  /\ pc' = [pc EXCEPT ![i] = "w2"]
  /\ UNCHANGED << num, choosing, max, nxt >>

w2self(i) ==
  /\ pc[i] = "w2"
  /\ read[i] <= NumProcs
  /\ LET j == read[i] IN
     /\ j = i
     /\ read' = [read EXCEPT ![i] = j + 1]
     /\ pc' = [pc EXCEPT ![i] = "w2"]
     /\ UNCHANGED << num, choosing, max, nxt >>

w2other(i) ==
  /\ pc[i] = "w2"
  /\ read[i] <= NumProcs
  /\ LET j == read[i] IN
     /\ j # i
     /\ choosing[j] = FALSE
     /\ (num[j] = 0) \/ (num[j] > num[i]) \/ (num[j] = num[i] /\ j > i)
     /\ read' = [read EXCEPT ![i] = j + 1]
     /\ pc' = [pc EXCEPT ![i] = "w2"]
     /\ UNCHANGED << num, choosing, max, nxt >>

w2done(i) ==
  /\ pc[i] = "w2"
  /\ read[i] > NumProcs
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << num, choosing, read, max, nxt >>

cs(i) ==
  /\ pc[i] = "cs"
  /\ num' = [num EXCEPT ![i] = 0]
  /\ pc' = [pc EXCEPT ![i] = "d1"]
  /\ UNCHANGED << choosing, read, max, nxt >>

Step(i) ==
  d1(i) \/ d2scan(i) \/ d2done(i) \/ d3(i)
  \/ w1(i) \/ w2self(i) \/ w2other(i) \/ w2done(i)
  \/ cs(i)

Next == \E i \in Proc: Step(i)

vars == << pc, num, choosing, read, max, nxt >>

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ pc \in [Proc -> {"d1","d2","d3","w1","w2","cs"}]
  /\ num \in [Proc -> Nat]
  /\ choosing \in [Proc -> BOOLEAN]
  /\ read \in [Proc -> Nat]
  /\ max \in [Proc -> Nat]
  /\ nxt \in [Proc -> Nat]

MutualExclusion ==
  \A i, j \in Proc: i # j => ~(pc[i] = "cs" /\ pc[j] = "cs")

TicketBound == \A i \in Proc: num[i] <= MaxNum
====