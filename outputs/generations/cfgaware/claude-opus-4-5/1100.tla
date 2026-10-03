------------------------------ MODULE MutualExclusion ------------------------------
EXTENDS Integers, TLC

(* --algorithm MutualExclusion
variables lock = "free";

process Proc \in {1, 2}
variables pc_local = "ncs";
begin
NCS:
    pc_local := "l1";
L1:
    await lock = "free";
    lock := "locked";
    pc_local := "cs";
CS:
    lock := "free";
    pc_local := "ncs";
    goto NCS;
end process;

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES lock, pc, pc_local

vars == << lock, pc, pc_local >>

ProcSet == {1, 2}

Init == (* Global variables *)
        /\ lock = "free"
        (* Process Proc *)
        /\ pc_local = [self \in ProcSet |-> "ncs"]
        /\ pc = [self \in ProcSet |-> "NCS"]

NCS(self) == /\ pc[self] = "NCS"
             /\ pc_local' = [pc_local EXCEPT ![self] = "l1"]
             /\ pc' = [pc EXCEPT ![self] = "L1"]
             /\ lock' = lock

L1(self) == /\ pc[self] = "L1"
            /\ lock = "free"
            /\ lock' = "locked"
            /\ pc_local' = [pc_local EXCEPT ![self] = "cs"]
            /\ pc' = [pc EXCEPT ![self] = "CS"]

CS(self) == /\ pc[self] = "CS"
            /\ lock' = "free"
            /\ pc_local' = [pc_local EXCEPT ![self] = "ncs"]
            /\ pc' = [pc EXCEPT ![self] = "NCS"]

Proc(self) == NCS(self) \/ L1(self) \/ CS(self)

Next == (\E self \in ProcSet: Proc(self))

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* END TRANSLATION

TypeOK == /\ lock \in {"free", "locked"}
          /\ pc \in [ProcSet -> {"NCS", "L1", "CS"}]
          /\ pc_local \in [ProcSet -> {"ncs", "l1", "cs"}]

LockInv == ~(pc[1] = "CS" /\ pc[2] = "CS")

Liveness == (pc[1] = "L1") ~> (pc[1] = "CS")

=============================================================================