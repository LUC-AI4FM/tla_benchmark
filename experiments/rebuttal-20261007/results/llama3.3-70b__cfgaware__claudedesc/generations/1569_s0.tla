```
MODULE CBakery

EXTENDS Integers

CONSTANT NumProcs, MaxNum

VARIABLE num, choosing
VARIABLE read, max, nxt

vars == <<num, choosing, read, max, nxt>>

Init ==
  /\ num = [i \in 1..NumProcs |-> 0]
  /\ choosing = [i \in 1..NumProcs |-> FALSE]
  /\ read = [i \in 1..NumProcs |-> {}]
  /\ max = [i \in 1..NumProcs |-> 0]
  /\ nxt = [i \in 1..NumProcs |-> 0]

d1(self) == 
  /\ choosing' = [choosing EXCEPT ![self] = TRUE]
  /\ read' = [read EXCEPT ![self] = {}]
  /\ max' = [max EXCEPT ![self] = 0]
  /\ nxt' = [nxt EXCEPT ![self] = 0]
  /\ UNCHANGED num

d2(self) == 
  /\ choosing' = choosing
  /\ read' = [read EXCEPT ![self] = {i \in 1..NumProcs : i # self}]
  /\ max' = [max EXCEPT ![self] = CHOOSE m \in Nat : m = 1 + Max({num[i] : i \in 1..NumProcs}))
  /\ nxt' = [nxt EXCEPT ![self] = max[self] + 1]
  /\ num' = [num EXCEPT ![self] = nxt[self]]
  /\ UNCHANGED choosing

d3(self) == 
  /\ choosing' = [choosing EXCEPT ![self] = FALSE]
  /\ UNCHANGED <<read, max, nxt, num>>

w1(self, other) == 
  /\ ~choosing[other]
  /\ num[other] # 0
  /\ (num[self] < num[other]) \/ (num[self] = num[other] /\ self < other)
  /\ UNCHANGED <<choosing, read, max, nxt, num>>

w2(self) == 
  /\ \A o \in 1..NumProcs : o # self => w1(self, o)
  /\ choosing' = choosing
  /\ read' = read
  /\ max' = max
  /\ nxt' = nxt
  /\ num' = num

cs(self) == 
  /\ \A o \in 1..NumProcs : o # self => w1(self, o)
  /\ num' = [num EXCEPT ![self] = 0]
  /\ UNCHANGED <<choosing, read, max, nxt>>

Next ==
  \E self \in 1..NumProcs :
    (d1(self)) \/ 
    (d2(self)) \/ 
    (d3(self)) \/ 
    (\E o \in 1..NumProcs : w1(self, o)) \/ 
    (w2(self)) \/ 
    (cs(self))

Spec == Init /\ [][Next]_vars

Invariant == \A s1, s2 \in 1..NumProcs : s1 # s2 => ~(num[s1] = num[s2] /\ choosing[s1] /\ choosing[s2])

THEOREM Spec => []Invariant
```
Note: The above TLA+ specification models Lamport's Bakery mutual exclusion algorithm for a configurable number of processes. It defines the required constants `NumProcs` and `MaxNum`, variables `num`, `choosing`, `read`, `max`, and `nxt`, and operators `Init`, `Next`, `Spec`, and `Invariant`. The specification captures the described behavior of the system, including the ticket-based priority scheme for accessing the critical section.