------------------------------- MODULE MutualExclusion -------------------------------
EXTENDS Integers, TLC

CONSTANTS ProcSet
VARIABLES lock, pc

(* --algorithm mutual_exclusion
variables lock = 1,
          pc = [p \in ProcSet |-> "l0"];

process (P \in ProcSet)
begin
l0: while TRUE do
        await pc[P] = "l0";
        pc[P] := "l1";
    l1:
        await pc[P] = "l1" /\ lock = 1;
        lock := 0;
        pc[P] := "cs";
    cs:
        await pc[P] = "cs";
        pc[P] := "l2";
    l2:
        await pc[P] = "l2";
        lock := 1;
        pc[P] := "l0";
end process;

end algorithm *)

Init == /\ lock = 1
        /\ \A p \in ProcSet: pc[p] = "l0"

TypeOK == /\ lock \in {0, 1}
          /\ \A p \in ProcSet: pc[p] \in {"l0", "l1", "cs", "l2"}

LockInv == \/ \E p \in ProcSet: pc[p] \in {"cs", "l2"} /\ lock = 0
           \/ \A p \in ProcSet: pc[p] \notin {"cs", "l2"}

Next ==
    \/ \E p \in ProcSet:
        \/ /\ pc[p] = "l0"
           /\ pc' = [pc EXCEPT ![p] = "l1"]
           /\ lock' = lock
        \/ /\ pc[p] = "l1" /\ lock = 1
           /\ pc' = [pc EXCEPT ![p] = "cs"]
           /\ lock' = 0
        \/ /\ pc[p] = "cs"
           /\ pc' = [pc EXCEPT ![p] = "l2"]
           /\ lock' = lock
        \/ /\ pc[p] = "l2"
           /\ pc' = [pc EXCEPT ![p] = "l0"]
           /\ lock' = 1

Spec == Init /\ [][Next]_<<lock, pc>>

THEOREM Spec => []TypeOK
THEOREM Spec => []LockInv
=============================================================================