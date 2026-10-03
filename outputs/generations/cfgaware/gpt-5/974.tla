----------------------------- MODULE RegularRing -----------------------------

EXTENDS Naturals

CONSTANT N

VARIABLES x, y, pc, clk, tC, tR

Proc == 1..N
Val == {0, 1}
XVal == {{0}, {0, 1}, {1}}
None == "None"

NextProc(i) == IF i < N THEN i + 1 ELSE 1

Init ==
  /\ N \in Nat /\ N >= 1
  /\ pc = [i \in Proc |-> "Write1"]
  /\ x = [i \in Proc |-> {0}]
  /\ y = [i \in Proc |-> None]
  /\ clk = 0
  /\ tC = [i \in Proc |-> 0]
  /\ tR = [i \in Proc |-> 0]

Write1(i) ==
  /\ i \in Proc
  /\ pc[i] = "Write1"
  /\ x[i] = {0}
  /\ x' = [x EXCEPT ![i] = {0, 1}]
  /\ pc' = [pc EXCEPT ![i] = "Write2"]
  /\ UNCHANGED << y, tC, tR >>
  /\ clk' = clk + 1

Write2(i) ==
  /\ i \in Proc
  /\ pc[i] = "Write2"
  /\ x[i] = {0, 1}
  /\ x' = [x EXCEPT ![i] = {1}]
  /\ pc' = [pc EXCEPT ![i] = "Read"]
  /\ tC' = [tC EXCEPT ![i] = clk + 1]
  /\ UNCHANGED << y, tR >>
  /\ clk' = clk + 1

Read(i) ==
  /\ i \in Proc
  /\ pc[i] = "Read"
  /\ \E r \in x[NextProc(i)]:
       y' = [y EXCEPT ![i] = r]
  /\ pc' = [pc EXCEPT ![i] = "Done"]
  /\ x' = x
  /\ tC' = tC
  /\ tR' = [tR EXCEPT ![i] = clk + 1]
  /\ clk' = clk + 1

Next == \E i \in Proc: Write1(i) \/ Write2(i) \/ Read(i)

vars == << x, y, pc, clk, tC, tR >>

Spec == Init /\ [][Next]_vars

Term == \A i \in Proc: pc[i] = "Done"

TypeOK ==
  /\ N \in Nat /\ N >= 1
  /\ x \in [Proc -> XVal]
  /\ y \in [Proc -> Val \cup {None}]
  /\ pc \in [Proc -> {"Write1", "Write2", "Read", "Done"}]
  /\ clk \in Nat
  /\ tC \in [Proc -> Nat]
  /\ tR \in [Proc -> Nat]

Inv ==
  /\ TypeOK
  /\ \A i \in Proc: (pc[i] \in {"Read", "Done"} => x[i] = {1})
  /\ \A i \in Proc: tR[i] = 0 \/ (tC[i] # 0 /\ tC[i] < tR[i])
  /\ \A i \in Proc: (y[i] = 0 /\ tR[i] # 0) => (tC[NextProc(i)] = 0 \/ tR[i] < tC[NextProc(i)])

PCorrect == Term => (\E i \in Proc: y[i] = 1)

THEOREM InvIsInvariant == Spec => []Inv
PROOF OBVIOUS QED

THEOREM PCorrectFromInv ==
  Inv /\ Term => \E i \in Proc: y[i] = 1
PROOF OBVIOUS QED

THEOREM PCorrectThm == Spec => []PCorrect
PROOF OBVIOUS QED

=============================================================================