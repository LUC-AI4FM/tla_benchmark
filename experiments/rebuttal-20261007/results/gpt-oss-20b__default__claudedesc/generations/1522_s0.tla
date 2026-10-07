MODULE HuangTermination
EXTENDS Naturals, Sequences, Integers

CONSTANTS Procs, Leader, MaxDenomExp

ASSUME Leader \in Procs

VARIABLES w, q, act

Scale == Power(2, MaxDenomExp)

Even(n) == Mod(n, 2) = 0

Init ==
  /\ w = [p \in Procs |-> IF p = Leader THEN Scale ELSE 0]
  /\ q = [p \in Procs |-> <<>>]
  /\ act = [p \in Procs |-> IF p = Leader THEN TRUE ELSE FALSE]

Send(p, r) ==
  /\ p \in Procs
  /\ r \in Procs \ {p}
  /\ w[p] >= 1
  /\ Even(w[p])
  /\ LET m == w[p] \div 2 IN
     /\ w' = [w EXCEPT ![p] = @ \div 2]
     /\ q' = [q EXCEPT ![r] = Append(q[r], m)]
     /\ act' = act

Receive(r) ==
  /\ r \in Procs \ {Leader}
  /\ Len(q[r]) > 0
  /\ LET m == Head(q[r]) IN
     /\ w' = [w EXCEPT ![r] = @ + m]
     /\ q' = [q EXCEPT ![r] = Tail(q[r])]
     /\ act' = [act EXCEPT ![r] = TRUE]

Idle(p) ==
  /\ p \in Procs \ {Leader}
  /\ w[p] > 0
  /\ LET m == w[p] IN
     /\ w' = [w EXCEPT ![p] = 0]
     /\ q' = [q EXCEPT ![Leader] = Append(q[Leader], m)]
     /\ act' = [act EXCEPT ![p] = FALSE]

IdleLdr ==
  /\ act[Leader] = TRUE
  /\ act' = [act EXCEPT ![Leader] = FALSE]
  /\ w' = w
  /\ q' = q

RcvLdr ==
  /\ Len(q[Leader]) > 0
  /\ LET m == Head(q[Leader]) IN
     /\ w' = [w EXCEPT ![Leader] = @