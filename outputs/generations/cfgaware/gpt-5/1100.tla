---- MODULE TwoProcLock ----
EXTENDS TLC

(*
--algorithm Lock2
variables lock = 0;

process (Proc \in {1,2})
begin
ncr: while TRUE do
        ncr: skip; \* non-critical section
l1:     await lock = 0;
        lock := self; \* acquire
cs:     skip; \* critical section
rel:    lock := 0; \* release
        goto ncr;
      end while;
end process

end algorithm
*)

CONSTANT Proc
ASSUME Proc = {1, 2}

VARIABLES lock, pc

vars == << lock, pc >>

Init ==
  /\ lock = 0
  /\ pc = [p \in Proc |-> "ncr"]

Ncr(self) ==
  /\ self \in Proc
  /\ pc[self] = "ncr"
  /\ pc' = [pc EXCEPT ![self] = "l1"]
  /\ UNCHANGED lock

Acquire(self) ==
  /\ self \in Proc
  /\ pc[self] = "l1"
  /\ lock = 0
  /\ lock' = self
  /\ pc' = [pc EXCEPT ![self] = "cs"]

Critical(self) ==
  /\ self \in Proc
  /\ pc[self] = "cs"
  /\ pc' = [pc EXCEPT ![self] = "rel"]
  /\ UNCHANGED lock

Release(self) ==
  /\ self \in Proc
  /\ pc[self] = "rel"
  /\ lock' = 0
  /\ pc' = [pc EXCEPT ![self] = "ncr"]

ProcStep(self) == Ncr(self) \/ Acquire(self) \/ Critical(self) \/ Release(self)

Next == \E self \in Proc: ProcStep(self)

Spec == Init /\ [][Next]_vars /\ \A self \in Proc: WF_vars(ProcStep(self))

TypeOK ==
  /\ lock \in ({0} \cup Proc)
  /\ pc \in [Proc -> {"ncr", "l1", "cs", "rel"}]

LockInv == ~(pc[1] = "cs" /\ pc[2] = "cs")

Live1 == (pc[1] = "l1") ~> (pc[1] = "cs")

====