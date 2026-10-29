---------------------------- MODULE Euclid ----------------------------
(***************************************************************************)
(* Subtraction-based Euclid's algorithm for the GCD.                       *)
(*                                                                         *)
(*   u := 24;  v :\in 1..50;                                               *)
(*   while (u # 0) {                                                       *)
(*     if (u < v) { u := v || v := u };                                    *)
(*     u := u - v                                                          *)
(*   }                                                                     *)
(*                                                                         *)
(* When u reaches 0, v holds GCD(24, v_ini). The main property is          *)
(* termination: every behavior eventually reaches pc = "Done".             *)
(***************************************************************************)
EXTENDS Integers, Naturals, TLC

CONSTANTS N, InitU

ASSUME /\ N \in Nat \ {0}
       /\ InitU \in Nat \ {0}

VARIABLES u, v, v_ini, pc

vars == << u, v, v_ini, pc >>

(* Helper definitions, used only to state the optional correctness check. *)
Divides(p, n) == \E q \in 0..n : n = p * q

GCD(m, n) ==
    CHOOSE i \in 1..m :
        /\ Divides(i, m)
        /\ Divides(i, n)
        /\ \A j \in 1..m : (Divides(j, m) /\ Divides(j, n)) => i >= j

TypeOK ==
    /\ u \in Int
    /\ v \in Int
    /\ v_ini \in 1..N
    /\ pc \in {"Lbl_1", "Lbl_2", "Done"}

Init ==
    /\ u = InitU
    /\ v \in 1..N
    /\ v_ini = v
    /\ pc = "Lbl_1"

(* Loop test: if u # 0, optionally swap so that u >= v, then go subtract. *)
Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ IF u # 0
          THEN /\ IF u < v
                     THEN /\ u' = v
                          /\ v' = u
                     ELSE UNCHANGED << u, v >>
               /\ pc' = "Lbl_2"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED << u, v >>
    /\ UNCHANGED v_ini

(* Subtract the second value from the first, then return to the loop test. *)
Lbl_2 ==
    /\ pc = "Lbl_2"
    /\ u' = u - v
    /\ pc' = "Lbl_1"
    /\ UNCHANGED << v, v_ini >>

(* Stuttering in the final state, so the model has no deadlock. *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Liveness: the algorithm always terminates (reaches the done state). *)
Termination == <>(pc = "Done")

(* Optional check: once done, v holds the GCD of the initial values. *)
PartialCorrectness == (pc = "Done") => (v = GCD(InitU, v_ini))

=============================================================================