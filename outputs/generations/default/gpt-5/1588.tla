------------------------------- MODULE EuclidSpec -------------------------------

EXTENDS Naturals, TLC

(*
--algorithm Euclid
variables u = 24, v \in 1..N, v_ini = v;
begin
Loop:
    while (u # v) do
        if (u < v) then
            swap: u, v := v, u;
        else
            sub: u := u - v;
        end if;
    end while;
Done:
    skip;
end algorithm;
*)

CONSTANT N

ASSUME N \in Nat /\ N >= 1

VARIABLES u, v, v_ini, pc

Vars == << u, v, v_ini, pc >>

Init ==
    /\ u = 24
    /\ v \in 1..N
    /\ v_ini = v
    /\ pc = "Loop"

Swap ==
    /\ pc = "Loop"
    /\ u # v
    /\ u < v
    /\ u' = v
    /\ v' = u
    /\ v_ini' = v_ini
    /\ pc' = "Loop"

Sub ==
    /\ pc = "Loop"
    /\ u # v
    /\ u >= v
    /\ u' = u - v
    /\ v' = v
    /\ v_ini' = v_ini
    /\ pc' = "Loop"

DoneStep ==
    /\ pc = "Loop"
    /\ u = v
    /\ pc' = "Done"
    /\ UNCHANGED << u, v, v_ini >>

Next == Swap \/ Sub \/ DoneStep

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

(*
 Safety invariants
*)
TypeInv ==
    /\ u \in Nat /\ u > 0
    /\ v \in Nat /\ v > 0
    /\ v_ini \in 1..N
    /\ pc \in {"Loop", "Done"}

Divides(d, x) == \E k \in Nat : x = d * k
CommonDivs(a, b) == { d \in 1..(a + b) : Divides(d, a) /\ Divides(d, b) }
GCD(a, b) == Max(CommonDivs(a, b))

ResultInv ==
    (pc = "Done") => /\ u = v /\ u = GCD(24, v_ini)

(*
 Liveness: termination (control eventually reaches Done)
*)
Termination == <> (pc = "Done")

=============================================================================