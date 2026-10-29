---------------------------- MODULE Euclid ----------------------------
EXTENDS Naturals, TLC

CONSTANT MaxNum

ASSUME MaxNum \in Nat /\ MaxNum > 0

CommonDivisors(x, y) == {i \in (1..x) \cap (1..y) : x % i = 0 /\ y % i = 0}

GCD(x, y) == CHOOSE i \in CommonDivisors(x, y) :
                \A j \in CommonDivisors(x, y) : i >= j

(***************************************************************************
--algorithm EuclidAlg {
    variables u_ini \in 1..MaxNum, v_ini \in 1..MaxNum,
              u = u_ini, v = v_ini;
    {
    a:  while (u # 0) {
            if (u < v) { u := v || v := u };
    b:      u := u - v
        };
        assert v = GCD(u_ini, v_ini)
    }
}
***************************************************************************)

VARIABLES pc, u, v, u_ini, v_ini

vars == << pc, u, v, u_ini, v_ini >>

Init == /\ u_ini \in 1..MaxNum
        /\ v_ini \in 1..MaxNum
        /\ u = u_ini
        /\ v = v_ini
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF u # 0
           THEN /\ IF u < v
                      THEN /\ u' = v
                           /\ v' = u
                      ELSE /\ UNCHANGED << u, v >>
                /\ pc' = "b"
           ELSE /\ Assert(v = GCD(u_ini, v_ini),
                          "Failure of assertion at line 22, column 9.")
                /\ pc' = "Done"
                /\ UNCHANGED << u, v >>
     /\ UNCHANGED << u_ini, v_ini >>

b == /\ pc = "b"
     /\ u' = u - v
     /\ pc' = "a"
     /\ UNCHANGED << v, u_ini, v_ini >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

Invariant == pc = "Done" => v = GCD(u_ini, v_ini)

-----------------------------------------------------------------------------
(* Coverage statistics *)

Finished == pc = "Done"

SwapOccurs == /\ pc = "a"
              /\ u # 0
              /\ u < v
              /\ pc' = "b"

ASSUME TLCSet(1, 0) /\ TLCSet(2, 0)

_POSSIBLE == /\ IF Finished' THEN TLCSet(1, TLCGet(1) + 1) ELSE TRUE
             /\ IF SwapOccurs THEN TLCSet(2, TLCGet(2) + 1) ELSE TRUE

PossibleCounts == /\ TLCGet(1) = 800
                  /\ TLCGet(2) = 698

=============================================================================