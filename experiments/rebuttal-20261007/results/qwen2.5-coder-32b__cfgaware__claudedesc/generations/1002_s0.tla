------------------------------- MODULE CyclicBarrier -------------------------------

CONSTANTS N

VARIABLES pc

(* --algorithm CyclicBarrier
variables pc = [p \in 1..N -> "b0"];

process Process(p \in 1..N)
begin
    while TRUE do
        await pc[p] = "b0";
        pc[p] := "b1";
        b0: skip;
        
        await \A q \in 1..N : pc[q] = "b1";
        b1: pc := [q \in 1..N -> "b0"];
    end while
end process; *)

Spec == /\ TYPEOK
        /\ BarrierProperty

TYPEOK == \A p \in 1..N : pc[p] \in {"b0", "b1"}

BarrierProperty ==
    \A s, t \in State: 
        \/ \E p \in 1..N : s.pc[p] = "b0"
            /\ \E q \in 1..N : s.pc[q] = "b1"
                /\ t = [s EXCEPT ![pc] = [q \in 1..N -> IF s.pc[q] = "b1" THEN "b1" ELSE "b0"]]
        \/ t = [s EXCEPT ![pc] = [p \in 1..N -> IF s.pc[p] = "b0" THEN "b1" ELSE s.pc[p]]]

State == [pc: [1..N -> {"b0", "b1"}}]

=============================================================================