---------------------------- MODULE MutualExclusion ----------------------------

EXTENDS Integers, Sequences, TLC

(* 
--algorithm MutualExclusion
variables lock = "free";

process Proc \in {1, 2}
variables pc_local = "ncs";
begin
ncs:
  while TRUE do
    l1:
      await lock = "free";
      lock := "self";
    cs:
      skip;
    l2:
      lock := "free";
  end while;
end process;

end algorithm;
*)

\* BEGIN TRANSLATION
VARIABLES lock, pc

vars == << lock, pc >>

ProcSet == ({1, 2})

Init == (* Global variables *)
        /\ lock = "free"
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "l1"]
             /\ lock' = lock

l1(self) == /\ pc[self] = "l1"
            /\ lock = "free"
            /\ lock' = [lock EXCEPT @ = self]
            /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ lock' = lock

l2(self) == /\ pc[self] = "l2"
            /\ lock' = "free"
            /\ pc' = [pc EXCEPT ![self] = "ncs"]

Proc(self) == ncs(self) \/ l1(self) \/ cs(self) \/ l2(self)

Next == (\E self \in {1, 2}: Proc(self))

Spec == Init /\ [][Next]_vars /\ \A self \in {1, 2} : WF_vars(Proc(self))

\* END TRANSLATION

-----------------------------------------------------------------------------

(* Type correctness invariant *)
TypeOK == /\ lock \in {"free"} \cup {1, 2}
          /\ pc \in [ProcSet -> {"ncs", "l1", "cs", "l2"}]

(* Mutual exclusion invariant: at most one process in critical section *)
LockInv == ~(pc[1] = "cs" /\ pc[2] = "cs")

(* Liveness property: if process 1 is waiting, it eventually enters cs *)
Liveness == (pc[1] = "l1") ~> (pc[1] = "cs")

=============================================================================