---------------------------- MODULE Euclid ----------------------------
EXTENDS Naturals, TLC

CONSTANT MaxNum

ASSUME MaxNumAssumption == MaxNum \in Nat /\ MaxNum > 0

(***************************************************************************)
(* Mathematical definition of GCD                                          *)
(***************************************************************************)
Divides(p, n) == \E q \in 0..n : n = p * q

DivisorsOf(n) == {p \in 1..n : Divides(p, n)}

SetMax(S) == CHOOSE x \in S : \A y \in S : x >= y

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))

(***************************************************************************)
(* PlusCal Algorithm (for reference):                                      *)
(*                                                                         *)
(* --algorithm Euclid                                                      *)
(*   variables u_ini \in 1..MaxNum, v_ini \in 1..MaxNum, u = u_ini, v = v_ini; *)
(* begin                                                                   *)
(*   while u /= v do                                                       *)
(*     if u > v then                                                       *)
(*       u := u - v;                                                       *)
(*     else                                                                *)
(*       v := v - u;                                                       *)
(*     end if;                                                             *)
(*   end while;                                                            *)
(* end algorithm                                                           *)
(***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES pc, u_ini, v_ini, u, v

vars == << pc, u_ini, v_ini, u, v >>

Init == /\ u_ini \in 1..MaxNum
        /\ v_ini \in 1..MaxNum
        /\ u = u_ini
        /\ v = v_ini
        /\ pc = "Loop"

Loop == /\ pc = "Loop"
        /\ IF u /= v
              THEN /\ IF u > v
                         THEN /\ u' = u - v
                              /\ v' = v
                         ELSE /\ v' = v - u
                              /\ u' = u
                   /\ pc' = "Loop"
              ELSE /\ pc' = "Done"
                   /\ UNCHANGED << u, v >>
        /\ UNCHANGED << u_ini, v_ini >>

Done == /\ pc = "Done"
        /\ UNCHANGED vars

Next == Loop \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

(***************************************************************************)
(* Invariant: When the algorithm terminates, u equals the GCD of the       *)
(* initial values                                                          *)
(***************************************************************************)
Invariant == pc = "Done" => u = GCD(u_ini, v_ini)

(***************************************************************************)
(* Additional useful properties                                            *)
(***************************************************************************)
TypeOK == /\ u_ini \in 1..MaxNum
          /\ v_ini \in 1..MaxNum
          /\ u \in 1..MaxNum
          /\ v \in 1..MaxNum
          /\ pc \in {"Loop", "Done"}

==========================================================================