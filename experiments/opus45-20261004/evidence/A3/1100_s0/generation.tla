---------------------------- MODULE MutualExclusion ----------------------------
EXTENDS Integers, TLC

CONSTANTS Proc

ASSUME Proc = {1, 2}

(*
--algorithm MutualExclusion
variables lock = "free";

process proc \in Proc
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

VARIABLES lock, pc

vars == << lock, pc >>

ProcSet == (Proc)

Init == (* Global variables *)
        /\ lock = "free"
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "l1"]
             /\ lock' = lock

l1(self) == /\ pc[self] = "l1"
            /\ lock = "free"
            /\ lock' = self
            /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ lock' = lock

l2(self) == /\ pc[self] = "l2"
            /\ lock' = "free"
            /\ pc' = [pc EXCEPT ![self] = "ncs"]

proc(self) == ncs(self) \/ l1(self) \/ cs(self) \/ l2(self)

Next == (\E self \in Proc: proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Proc : WF_vars(proc(self))

-----------------------------------------------------------------------------

(* Type correctness invariant *)
TypeOK == /\ lock \in {"free"} \cup Proc
          /\ pc \in [Proc -> {"ncs", "l1", "cs", "l2"}]

(* Mutual exclusion invariant: at most one process in critical section *)
MutualExclusion == ~(pc[1] = "cs" /\ pc[2] = "cs")

(* Liveness property: if process 1 is waiting, it eventually enters critical section *)
Liveness == (pc[1] = "l1") ~> (pc[1] = "cs")

=============================================================================