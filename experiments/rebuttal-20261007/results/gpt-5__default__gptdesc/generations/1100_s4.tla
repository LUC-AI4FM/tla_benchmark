----------------------------- MODULE LockTwo -----------------------------

EXTENDS Naturals

CONSTANT ProcIds
ASSUME ProcIds = {1, 2}

(*
--algorithm LockTwoPlusCal
variables lock = 0;

process (P \in ProcIds)
begin
ncs:
  if P = 1 then
    goto l1;
  else
    goto l2;
  end if;

l1:
  if lock = 0 then
    lock := 1;
    goto cs;
  else
    goto l1;
  end if;

l2:
  if lock = 0 then
    lock := 2;
    goto cs;
  else
    goto l2;
  end if;

cs:
  skip;

rel:
  lock := 0;
  goto ncs;
end process;

end algorithm;
*)

VARIABLES lock, pc

Proc == ProcIds
Labels == {"ncs", "l1", "l2", "cs", "rel"}

vars == << lock, pc >>

Init ==
  /\ lock = 0
  /\ pc \in [Proc -> Labels]
  /\ pc = [p \in Proc |-> "ncs"]

Ncs(self) ==
  /\ self \in Proc
  /\ pc[self] = "ncs"
  /\ pc' = [pc EXCEPT ![self] = IF self = 1 THEN "l1" ELSE "l2"]
  /\ UNCHANGED lock

L1Acquire ==
  /\ pc[1] = "l1"
  /\ lock = 0
  /\ lock' = 1
  /\ pc' = [pc EXCEPT ![1] = "cs"]

L2Acquire ==
  /\ pc[2] = "l2"
  /\ lock = 0
  /\ lock' = 2
  /\ pc' = [pc EXCEPT ![2] = "cs"]

Cs(self) ==
  /\ self \in Proc
  /\ pc[self] = "cs"
  /\ pc' = [pc EXCEPT ![self] = "rel"]
  /\ UNCHANGED lock

Rel(self) ==
  /\ self \in Proc
  /\ pc[self] = "rel"
  /\ lock' = 0
  /\ pc' = [pc EXCEPT ![self] = "ncs"]

Next ==
  \/ \E self \in Proc: Ncs(self)
  \/ L1Acquire
  \/ L2Acquire
  \/ \E self \in Proc: Cs(self)
  \/ \E self \in Proc: Rel(self)

Spec ==
  Init /\ [][Next]_vars

TypeOK ==
  /\ lock \in {0} \cup Proc
  /\ pc \in [Proc -> Labels]

MutualExclusion ==
  ~(\E p1, p2 \in Proc: p1 # p2 /\ pc[p1] = "cs" /\ pc[p2] = "cs")

Safety == TypeOK /\ MutualExclusion

Liveness ==
  [](pc[1] = "l1" => <> pc[1] = "cs")

=============================================================================