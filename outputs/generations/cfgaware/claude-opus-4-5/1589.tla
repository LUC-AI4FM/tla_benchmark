---------------------------- MODULE Euclid ----------------------------
EXTENDS Integers, TLC

CONSTANT MaxNum

ASSUME MaxNumAssumption == MaxNum \in Nat \ {0}

(* PlusCal algorithm for Euclid's GCD

--algorithm Euclid
variables u_ini \in 1..MaxNum, v_ini \in 1..MaxNum, u = u_ini, v = v_ini;
begin
  while u /= 0 do
    if u < v then
      u := v || v := u
    end if;
    u := u - v
  end while
end algorithm

*)

\* BEGIN TRANSLATION
VARIABLES pc, u_ini, v_ini, u, v

vars == << pc, u_ini, v_ini, u, v >>

Init == (* Global variables *)
        /\ u_ini \in 1..MaxNum
        /\ v_ini \in 1..MaxNum
        /\ u = u_ini
        /\ v = v_ini
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF u /= 0
               THEN /\ IF u < v
                          THEN /\ /\ u' = v
                                  /\ v' = u
                          ELSE /\ TRUE
                               /\ UNCHANGED << u, v >>
                    /\ pc' = "Lbl_2"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << u, v >>
         /\ UNCHANGED << u_ini, v_ini >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ u' = u - v
         /\ pc' = "Lbl_1"
         /\ UNCHANGED << u_ini, v_ini, v >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* END TRANSLATION

(* Mathematical definition of GCD *)
Divides(p, n) == \E q \in 0..n : n = p * q

DivisorsOf(n) == {p \in 1..n : Divides(p, n)}

SetMax(S) == CHOOSE x \in S : \A y \in S : x >= y

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))

(* Termination property *)
Termination == <>(pc = "Done")

(* Invariant: when algorithm terminates, v holds the GCD of original inputs *)
Invariant == pc = "Done" => v = GCD(u_ini, v_ini)

==========================================================================