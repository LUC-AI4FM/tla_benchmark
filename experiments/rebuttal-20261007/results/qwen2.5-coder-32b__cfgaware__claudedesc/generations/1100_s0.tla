---- MODULE MutualExclusion ----

CONSTANTS Proc \* Set of processes {1, 2}

VARIABLES lock, pc

(*--algorithm mutual_exclusion
variables lock = 1,
          pc = [p \in Proc |-> "l0"];

process (p \in Proc)
begin
l0: while TRUE do
        await pc[p] = "l0";
        pc[p] := "l1";

    l1: await pc[p] = "l1" /\ lock = 1;
        lock := 0;
        pc[p] := "cs";

    cs: await pc[p] = "cs";
        pc[p] := "l2";

    l2: await pc[p] = "l2";
        lock := 1;
        pc[p] := "l0"
end process;

end algorithm;*)

Spec == /\ Init
         /\ [][Next]_<<lock, pc>>

Init == /\ lock = 1
        /\ \A p \in Proc: pc[p] = "l0"

Next ==
    \/ \E p \in Proc: Action(p)

Action(p) ==
    \/ /\ pc[p] = "l0"
       /\ pc' = [pc EXCEPT ![p] = "l1"]
       /\ lock' = lock
    \/ /\ pc[p] = "l1"
       /\ lock = 1
       /\ pc' = [pc EXCEPT ![p] = "cs"]
       /\ lock' = 0
    \/ /\ pc[p] = "cs"
       /\ pc' = [pc EXCEPT ![p] = "l2"]
       /\ lock' = lock
    \/ /\ pc[p] = "l2"
       /\ pc' = [pc EXCEPT ![p] = "l0"]
       /\ lock' = 1

TypeOK ==
    /\ lock \in {0, 1}
    /\ \A p \in Proc: pc[p] \in {"l0", "l1", "cs", "l2"}

LockInv ==
    \/ ~(\E p \in Proc: pc[p] \in {"cs", "l2"})
    \/ (\E p \in Proc: pc[p] \in {"cs", "l2"} /\ lock = 0)

THEOREM Spec => []TypeOK
<1>1. Init => TypeOK
<1>2. \A s, s' \in State: s -(:> Next :)- s' => TypeOK(s) => TypeOK(s')
    BY <1>1, <1>2 DEF Spec, Init, Next

THEOREM Spec => []LockInv
<1>1. Init => LockInv
<1>2. \A s, s' \in State: s -(:> Next :)- s' => LockInv(s) => LockInv(s')
    BY <1>1, <1>2 DEF Spec, Init, Next

====