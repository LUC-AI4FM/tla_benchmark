------------------------------ MODULE Fischer ------------------------------
EXTENDS Naturals

CONSTANTS N, Delta, Epsilon

ASSUME /\ N \in Nat /\ N > 0
       /\ Delta \in Nat /\ Epsilon \in Nat
       /\ Delta < Epsilon

Proc == 1..N
Labels == {"a","b","c","d","e","cs","f"}

VARIABLES x, timer, pc, haveSetEps

vars == << x, timer, pc, haveSetEps >>

TypeOK ==
  /\ x \in 0..N
  /\ timer \in [Proc -> Nat]
  /\ pc \in [Proc -> Labels]
  /\ haveSetEps \in [Proc -> BOOLEAN]

Init ==
  /\ x = 0
  /\ timer = [i \in Proc |-> 0]
  /\ pc = [i \in Proc |-> "a"]
  /\ haveSetEps = [i \in Proc |-> FALSE]

A2B(i) ==
  /\ pc[i] = "a"
  /\ pc' = [pc EXCEPT ![i] = "b"]
  /\ UNCHANGED << x, timer, haveSetEps >>

B2CS(i) ==
  /\ pc[i] = "b"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, timer, haveSetEps >>

B2C(i) ==
  /\ pc[i] = "b"
  /\ x # i
  /\ pc' = [pc EXCEPT ![i] = "c"]
  /\ UNCHANGED << x, timer, haveSetEps >>

C2D(i) ==
  /\ pc[i] = "c"
  /\ x = 0
  /\ pc' = [pc EXCEPT ![i] = "d"]
  /\ UNCHANGED << x, timer, haveSetEps >>

D2E(i) ==
  /\ pc[i] = "d"
  /\ x' = i
  /\ timer' = [timer EXCEPT ![i] = Delta]
  /\ haveSetEps' = [haveSetEps EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "e"]

ESet(i) ==
  /\ pc[i] = "e"
  /\ haveSetEps[i] = FALSE
  /\ timer' = [timer EXCEPT ![i] = Epsilon]
  /\ haveSetEps' = [haveSetEps EXCEPT ![i] = TRUE]
  /\ UNCHANGED << x, pc >>

EWait(i) ==
  /\ pc[i] = "e"
  /\ haveSetEps[i] = TRUE
  /\ timer[i] = 0
  /\ pc' = [pc EXCEPT ![i] = "b"]
  /\ haveSetEps' = [haveSetEps EXCEPT ![i] = FALSE]
  /\ UNCHANGED << x, timer >>

CS2F(i) ==
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "f"]
  /\ UNCHANGED << x, timer, haveSetEps >>

F2A(i) ==
  /\ pc[i] = "f"
  /\ x' = 0
  /\ pc' = [pc EXCEPT ![i] = "a"]
  /\ UNCHANGED << timer, haveSetEps >>

ProcSteps(i) ==
  A2B(i) \/ B2CS(i) \/ B2C(i) \/ C2D(i) \/
  D2E(i) \/ ESet(i) \/ EWait(i) \/ CS2F(i) \/ F2A(i)

Tick ==
  /\ \A j \in Proc: timer[j] > 0
  /\ timer' = [j \in Proc |-> timer[j] - 1]
  /\ UNCHANGED << x, pc, haveSetEps >>

Next ==
  Tick \/ (\E i \in Proc: ProcSteps(i))

Spec ==
  Init /\ [][Next]_vars /\
  WF_vars(Tick) /\ (\A i \in Proc: WF_vars(ProcSteps(i)))

Invariant ==
  \A i, j \in Proc: (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

SomeInCS ==
  \E i \in Proc: pc[i] = "cs"

Liveness ==
  []<>(SomeInCS)
============================================================================