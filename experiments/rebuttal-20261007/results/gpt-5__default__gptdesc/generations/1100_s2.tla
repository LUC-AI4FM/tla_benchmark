----------------------------- MODULE TwoProcLock -----------------------------
EXTENDS Naturals

CONSTANTS ProcSet
ASSUME ProcSet = {1, 2}

(*
--algorithm TwoProcLock
variables owner = 0;

process (Proc \in ProcSet)
begin
nc:
  goto l1;

l1:
  await owner = 0;
  owner := self;
  goto cs;

cs:
  skip;

release:
  owner := 0;
  goto nc;
end process;

end algorithm
*)

VARIABLES owner, pc

Vars == << owner, pc >>

TypeInv ==
  /\ owner \in {0} \cup ProcSet
  /\ pc \in [ProcSet -> {"nc", "l1", "cs", "release"}]

MutualExclusion ==
  \A p, q \in ProcSet : p # q => ~(pc[p] = "cs" /\ pc[q] = "cs")

Safety == TypeInv /\ MutualExclusion

Init ==
  /\ owner = 0
  /\ pc = [p \in ProcSet |-> "nc"]

Next ==
  \E self \in ProcSet :
    \/ /\ pc[self] = "nc"
       /\ pc' = [pc EXCEPT ![self] = "l1"]
       /\ UNCHANGED owner
    \/ /\ pc[self] = "l1"
       /\ owner = 0
       /\ pc' = [pc EXCEPT ![self] = "cs"]
       /\ owner' = self
    \/ /\ pc[self] = "cs"
       /\ pc' = [pc EXCEPT ![self] = "release"]
       /\ UNCHANGED owner
    \/ /\ pc[self] = "release"
       /\ pc' = [pc EXCEPT ![self] = "nc"]
       /\ owner' = 0

Spec == Init /\ [][Next]_Vars

Liveness ==
  (pc[1] = "l1") ~> (pc[1] = "cs")
=============================================================================