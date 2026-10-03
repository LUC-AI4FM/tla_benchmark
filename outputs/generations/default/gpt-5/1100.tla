----------------------------- MODULE TwoProcLock -----------------------------

EXTENDS Naturals

CONSTANTS ProcSet
ASSUME ProcSet = {1, 2}

(*
--algorithm LockAlg
variables lock = 0;

process (p \in ProcSet)
begin
n:  while TRUE do
       l1: await lock = 0;
           lock := self;
       cs: skip;
       rel: lock := 0;
     end while;
end process;

end algorithm
*)

(*
TLA+ translation of the PlusCal algorithm
*)

VARIABLES pc, lock

vars == << pc, lock >>

Init ==
  /\ pc = [p \in ProcSet |-> "n"]
  /\ lock = 0

Proc(p) ==
  \/ /\ pc[p] = "n"
     /\ pc' = [pc EXCEPT ![p] = "l1"]
     /\ UNCHANGED lock
  \/ /\ pc[p] = "l1"
     /\ lock = 0
     /\ lock' = p
     /\ pc' = [pc EXCEPT ![p] = "cs"]
  \/ /\ pc[p] = "cs"
     /\ pc' = [pc EXCEPT ![p] = "rel"]
     /\ UNCHANGED lock
  \/ /\ pc[p] = "rel"
     /\ lock' = 0
     /\ pc' = [pc EXCEPT ![p] = "n"]

Next ==
  \E p \in ProcSet: Proc(p)

Spec ==
  Init /\ [][Next]_vars

TypeOK ==
  /\ pc \in [ProcSet -> {"n", "l1", "cs", "rel"}]
  /\ lock \in ({0} \cup ProcSet)

MutualExclusion ==
  \A p \in ProcSet: \A q \in ProcSet:
    (p # q) => ~(/\ pc[p] = "cs" /\ pc[q] = "cs")

Live ==
  (pc[1] = "l1") ~> (pc[1] = "cs")

=============================================================================