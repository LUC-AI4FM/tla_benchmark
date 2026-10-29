---------------------------- MODULE Euclid ----------------------------
EXTENDS Naturals, TLC

CONSTANT MaxNum

ASSUME MaxNumAssump == MaxNum \in Nat \ {0}

(***************************************************************************)
(* Mathematical definition of the greatest common divisor.                *)
(***************************************************************************)
Divides(p, n) == \E q \in 1..n : n = p * q

DivisorsOf(n) == {p \in 1..n : Divides(p, n)}

SetMax(S) == CHOOSE x \in S : \A y \in S : x >= y

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))

(***************************************************************************
--algorithm Euclid
  variables u_ini \in 1..MaxNum,
            v_ini \in 1..MaxNum,
            u = u_ini,
            v = v_ini;
  begin
  L1: while u # 0 do
        if u < v then
          u := v || v := u;
        end if;
  L2:   u := u - v;
      end while;
end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES u_ini, v_ini, u, v, pc

vars == << u_ini, v_ini, u, v, pc >>

Init == /\ u_ini \in 1..MaxNum
        /\ v_ini \in 1..MaxNum
        /\ u = u_ini
        /\ v = v_ini
        /\ pc = "L1"

L1 == /\ pc = "L1"
      /\ IF u # 0
            THEN /\ IF u < v
                       THEN /\ u' = v
                            /\ v' = u
                       ELSE /\ UNCHANGED << u, v >>
                 /\ pc' = "L2"
            ELSE /\ pc' = "Done"
                 /\ UNCHANGED << u, v >>
      /\ UNCHANGED << u_ini, v_ini >>

L2 == /\ pc = "L2"
      /\ u' = u - v
      /\ pc' = "L1"
      /\ UNCHANGED << u_ini, v_ini, v >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == L1 \/ L2 \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

(***************************************************************************)
(* Correctness: on termination, v holds the GCD of the initial values.    *)
(***************************************************************************)
Invariant == (pc = "Done") => (v = GCD(u_ini, v_ini))

(***************************************************************************)
(* Named properties whose reachability is counted with TLC registers.     *)
(***************************************************************************)
Finished == pc = "Done"

SwapOccurs == pc = "L1" /\ u # 0 /\ u < v

ASSUME TLCSet(1, 0)
ASSUME TLCSet(2, 0)

(* State constraint that counts the states satisfying each property. *)
PossibleCounts ==
    /\ IF Finished THEN TLCSet(1, TLCGet(1) + 1) ELSE TRUE
    /\ IF SwapOccurs THEN TLCSet(2, TLCGet(2) + 1) ELSE TRUE

(* Postcondition: each named property must be satisfied by some state. *)
_POSSIBLE == /\ TLCGet(1) > 0
             /\ TLCGet(2) > 0

=============================================================================