----------------------------- MODULE TwoProcMutex -----------------------------
EXTENDS Naturals

CONSTANT Proc

ASSUME Proc = {1, 2}

(*
--algorithm Mutex
variables lock = "free";

process (p \in Proc)
begin
ncs:
  goto l1;

l1:
  await lock = "free";
  lock := self;
  goto cs;

cs:
  goto rel;

rel:
  lock := "free";
  goto ncs;
end process;

end algorithm
*)

VARIABLES pc, lock

vars == << pc, lock >>

Init ==
  /\ lock = "free"
  /\ pc = [p \in Proc |-> "ncs"]

ncs(p) ==
  /\ p \in Proc
  /\ pc[p] = "ncs"
  /\ pc' = [pc EXCEPT ![p] = "l1"]
  /\ UNCHANGED lock

l1(p) ==
  /\ p \in Proc
  /\ pc[p] = "l1"
  /\ lock = "free"
  /\ lock' = p
  /\ pc' = [pc EXCEPT ![p] = "cs"]

cs(p) ==
  /\ p \in Proc
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "rel"]
  /\ UNCHANGED lock

rel(p) ==
  /\ p \in Proc
  /\ pc[p] = "rel"
  /\ lock' = "free"
  /\ pc' = [pc EXCEPT ![p] = "ncs"]

Next ==
  ∃ p \in Proc:
       ncs(p)
    \/ l1(p)
    \/ cs(p)
    \/ rel(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ lock \in {"free"} \cup Proc
  /\ pc \in [Proc -> {"ncs", "l1", "cs", "rel"}]

MutualExclusion ==
  ∀ p \in Proc: ∀ q \in Proc:
    p # q => ~(pc[p] = "cs" /\ pc[q] = "cs")

Inv == TypeOK /\ MutualExclusion

Liveness ==
  (pc[1] = "l1") ~> (pc[1] = "cs")
=============================================================================