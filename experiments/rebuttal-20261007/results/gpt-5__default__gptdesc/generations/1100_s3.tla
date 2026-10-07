----------------------------- MODULE TwoProcMutex -----------------------------
EXTENDS TLC

CONSTANTS ProcSet

ASSUME ProcSet = {1, 2}

(*
--algorithm Mutex
variables lock = FALSE;

process (P \in ProcSet)
begin
n:
  while TRUE do
    l1:
      await ~lock;
      lock := TRUE;
    cs:
      skip;
    l2:
      lock := FALSE;
  end while;
end process;

end algorithm
*)

VARIABLES lock, pc

vars == << lock, pc >>

Init ==
  /\ lock = FALSE
  /\ pc = [self \in ProcSet |-> "n"]

N(self) ==
  /\ pc[self] = "n"
  /\ pc' = [pc EXCEPT ![self] = "l1"]
  /\ UNCHANGED lock

L1(self) ==
  /\ pc[self] = "l1"
  /\ ~lock
  /\ lock' = TRUE
  /\ pc' = [pc EXCEPT ![self] = "cs"]

CS(self) ==
  /\ pc[self] = "cs"
  /\ pc' = [pc EXCEPT ![self] = "l2"]
  /\ UNCHANGED lock

L2(self) ==
  /\ pc[self] = "l2"
  /\ lock' = FALSE
  /\ pc' = [pc EXCEPT ![self] = "n"]

Next ==
  \E self \in ProcSet:
      N(self) \/ L1(self) \/ CS(self) \/ L2(self)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ lock \in BOOLEAN
  /\ pc \in [ProcSet -> {"n", "l1", "cs", "l2"}]

MutexInv ==
  ~(pc[1] = "cs" /\ pc[2] = "cs")

Liveness ==
  (pc[1] = "l1") ~> (pc[1] = "cs")
=============================================================================