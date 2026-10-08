------------------------------- MODULE TwoProcessIncrement -------------------------------

EXTENDS Naturals, TLC

CONSTANTS ProcA, ProcB

VARIABLES x, pc

(* --algorithm two_process_increment
variables x = 0;

process (ProcA)
begin
    increment:
        x := x + 1;
    end increment;
    Done:
        skip;
end process;

process (ProcB)
begin
    increment:
        x := x + 1;
    end increment;
    Done:
        skip;
end process;
end algorithm *)

Init == /\ x = 0
        /\ pc[ProcA] = "increment"
        /\ pc[ProcB] = "increment"

Next ==
    \/ /\ pc[ProcA] = "increment"
       /\ \E x': x' = x + 1
          /\ UNCHANGED [pc EXCEPT ![ProcB]]
          /\ pc'[ProcA] = "Done"
          /\ x' = x
    \/ /\ pc[ProcB] = "increment"
       /\ \E x': x' = x + 1
          /\ UNCHANGED [pc EXCEPT ![ProcA]]
          /\ pc'[ProcB] = "Done"
          /\ x' = x
    \/ /\ pc[ProcA] = "Done"
       /\ pc[ProcB] = "Done"
       /\ pc' = pc
       /\ x' = x

Spec ==
    WF_vars == <<pc, x>>
    Spec_0 == Init /\ [][Next]_<<x, pc>> /\ <>[]<>(pc[ProcA] = "Done" /\ pc[ProcB] = "Done")
    Spec == Spec_0

Terminating ==
    \/ pc[ProcA] = "Done"
    \/ pc[ProcB] = "Done"

=============================================================================