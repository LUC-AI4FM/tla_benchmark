----------------------------- MODULE Fischer -----------------------------
EXTENDS Naturals

CONSTANTS Proc, Delta, Epsilon

ASSUME
  /\ Proc \subseteq Nat
  /\ Proc # {}
  /\ Delta \in Nat \ {0}
  /\ Epsilon \in Nat \ {0}

VARIABLES lock, pc, tmr

vars == << lock, pc, tmr >>

PCVals == {"idle", "afterSet", "waitEps", "check", "cs"}

TypeOK ==
  /\ lock \in Proc \cup {0}
  /\ pc \in [Proc -> PCVals]
  /\ tmr \in [Proc -> Nat]

Init ==
  /\ lock = 0
  /\ pc = [p \in Proc |-> "idle"]
  /\ tmr = [p \in Proc |-> 0]

TryEnter(p) ==
  /\ p \in Proc
  /\ pc[p] = "idle"
  /\ lock = 0
  /\ lock' = p
  /\ pc' = [pc EXCEPT ![p] = "afterSet"]
  /\ tmr' = [tmr EXCEPT ![p] = Delta]

ResetToEps(p) ==
  /\ p \in Proc
  /\ pc[p] = "afterSet"
  /\ tmr[p] = 0
  /\ pc' = [pc EXCEPT ![p] = "waitEps"]
  /\ tmr' = [tmr EXCEPT ![p] = Epsilon]
  /\ UNCHANGED lock

EpsExpired(p) ==
  /\ p \in Proc
  /\ pc[p] = "waitEps"
  /\ tmr[p] = 0
  /\ pc' = [pc EXCEPT ![p] = "check"]
  /\ UNCHANGED << lock, tmr >>

CheckWin(p) ==
  /\ p \in Proc
  /\ pc[p] = "check"
  /\ lock = p
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED << lock, tmr >>

CheckLose(p) ==
  /\ p \in Proc
  /\ pc[p] = "check"
  /\ lock # p
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED << lock, tmr >>

ExitCS(p) ==
  /\ p \in Proc
  /\ pc[p] = "cs"
  /\ lock' = 0
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED tmr

ProcStep(p) ==
  TryEnter(p)
  \/ ResetToEps(p)
  \/ EpsExpired(p)
  \/ CheckWin(p)
  \/ CheckLose(p)
  \/ ExitCS(p)

Clock ==
  /\ \E p \in Proc: tmr[p] > 0
  /\ tmr' = [p \in Proc |-> IF tmr[p] > 0 THEN tmr[p] - 1 ELSE 0]
  /\ UNCHANGED << lock, pc >>

Next ==
  \/ \E p \in Proc: ProcStep(p)
  \/ Clock

Mutex ==
  \A p, q \in Proc: p # q => ~(pc[p] = "cs" /\ pc[q] = "cs")

Safety == Mutex

Liveness == []<>(\E p \in Proc: pc[p] = "cs")

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ (\A p \in Proc: WF_vars(ProcStep(p)))
  /\ WF_vars(Clock)
============================================================================