---- MODULE SimpleConcurrentIncrement ----

CONSTANTS ProcA, ProcB

VARIABLES x, pc

(*--algorithm SimpleConcurrentIncrement
variables x = 0;
begin
    with \* Process A
        a:
            x := x + 1;
            pc[ProcA] := "Done";
    endwith;

    with \* Process B
        b:
            x := x + 1;
            pc[ProcB] := "Done";
    endwith;

    Terminating:
        skip;
end algorithm;*)

Init == /\ x = 0
        /\ pc = [ProcA |-> "", ProcB |-> ""]

Next ==
    \/ /\ pc[ProcA] = ""
       /\ \E newPc \in {"a", "Done"} :
            /\ pc' = [pc EXCEPT ![ProcA] = newPc]
            /\ x' = IF newPc = "a" THEN x + 1 ELSE x
    \/ /\ pc[ProcB] = ""
       /\ \E newPc \in {"b", "Done"} :
            /\ pc' = [pc EXCEPT ![ProcB] = newPc]
            /\ x' = IF newPc = "b" THEN x + 1 ELSE x
    \/ /\ pc[ProcA] = "Done"
       /\ pc[ProcB] = "Done"
       /\ UNCHANGED <<x, pc>>

Spec == Init /\ [][Next]_<<x, pc>>

Termination ==
    <>(/\ pc[ProcA] = "Done"
        /\ pc[ProcB] = "Done")

====