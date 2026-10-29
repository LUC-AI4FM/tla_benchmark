------------------------------- MODULE Euclid -------------------------------
EXTENDS Naturals, TLC

(***************************************************************************
--algorithm Euclid
variables u = 24, v \in 1 .. 50;
begin
Lbl_1:
  while u # 0 do
    if u < v then
      u := v || v := u;
    end if;
Lbl_2:
    u := u - v;
  end while;
end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES u, v, pc

vars == << u, v, pc >>

Init == (* Global variables *)
        /\ u = 24
        /\ v \in 1 .. 50
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF u # 0
               THEN /\ IF u < v
                          THEN /\ /\ u' = v
                                  /\ v' = u
                          ELSE /\ TRUE
                               /\ UNCHANGED << u, v >>
                    /\ pc' = "Lbl_2"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << u, v >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ u' = u - v
         /\ pc' = "Lbl_1"
         /\ v' = v

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK == /\ u \in Nat
          /\ v \in Nat
          /\ pc \in {"Lbl_1", "Lbl_2", "Done"}

\* v always stays positive, so subtraction never makes u negative
VPositive == v > 0

\* Before subtracting, u >= v holds
SubtractSafe == (pc = "Lbl_2") => (u >= v)

\* Divisibility-based gcd definitions
Divides(p, n) == \E q \in 0 .. n : n = q * p
DivisorsOf(n) == {p \in 1 .. 50 : Divides(p, n)}
GCD(m, n) == CHOOSE i \in DivisorsOf(m) \cap DivisorsOf(n) :
                \A j \in DivisorsOf(m) \cap DivisorsOf(n) : i >= j

\* On termination u = 0 and v holds the gcd, which divides 24
PartialCorrectness == (pc = "Done") => /\ u = 0
                                       /\ v > 0
                                       /\ Divides(v, 24)

-----------------------------------------------------------------------------
(* Liveness (requires weak fairness on Next) *)

FairSpec == Spec /\ WF_vars(Next)

=============================================================================