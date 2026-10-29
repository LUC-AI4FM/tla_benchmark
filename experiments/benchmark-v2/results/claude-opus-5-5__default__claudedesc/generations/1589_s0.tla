---- MODULE Euclid ----
EXTENDS Naturals, TLC

CONSTANT MaxNum

ASSUME MaxNumAssumption == MaxNum = 20

GCD(x, y) ==
    CHOOSE i \in (1..x) \cap (1..y) :
        /\ x % i = 0
        /\ y % i = 0
        /\ \A j \in (1..x) \cap (1..y) :
               (x % j = 0 /\ y % j = 0) => i >= j

VARIABLES pc, u, v, u_ini, v_ini

vars == << pc, u, v, u_ini, v_ini >>

Init ==
    /\ u_ini \in 1..MaxNum
    /\ v_ini \in 1..MaxNum
    /\ u = u_ini
    /\ v = v_ini
    /\ pc = "a"

a ==
    /\ pc = "a"
    /\ IF u # 0
          THEN /\ IF u < v
                     THEN /\ u' = v
                          /\ v' = u
                     ELSE /\ UNCHANGED << u, v >>
               /\ pc' = "b"
          ELSE /\ Assert(v = GCD(u_ini, v_ini),
                         "Failure of assertion at label a.")
               /\ pc' = "Done"
               /\ UNCHANGED << u, v >>
    /\ UNCHANGED << u_ini, v_ini >>

b ==
    /\ pc = "b"
    /\ u' = u - v
    /\ pc' = "a"
    /\ UNCHANGED << v, u_ini, v_ini >>

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == a \/ b \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

Invariant == (pc = "Done") => (v = GCD(u_ini, v_ini))

-----------------------------------------------------------------------------
(* Coverage statistics: predicates whose occurrence counts are checked.     *)

Finished == pc = "Done"

SwapOccurs == pc = "a" /\ u # 0 /\ u < v

(* Counting via TLC registers 1 (Finished) and 2 (SwapOccurs).             *)
(* Registers are initialised once and incremented as an ACTION_CONSTRAINT. *)

ASSUME TLCSet(1, 0) /\ TLCSet(2, 0)

CountCoverage ==
    /\ IF Finished THEN TLCSet(1, TLCGet(1) + 1) ELSE TRUE
    /\ IF SwapOccurs THEN TLCSet(2, TLCGet(2) + 1) ELSE TRUE

PossibleCounts ==
    /\ TLCGet(1) = 800
    /\ TLCGet(2) = 698

=============================================================================